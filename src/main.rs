use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::Fp;
use halo2_proofs::{arithmetic::FieldExt, circuit::Value, circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct FibonacciConfig {
    pub advice: [Column<Advice>; 5],
    pub selector: Selector,
    pub xor_table: [TableColumn; 3],
    pub instance: Column<Instance>,
}

impl FibonacciConfig {
    pub fn configure<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let col_d = meta.advice_column();
        let col_e = meta.advice_column();
        let instance = meta.instance_column();
        let s = meta.complex_selector();

        let xor_table = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(col_d);
        meta.enable_equality(col_e);
        meta.enable_equality(instance);

        meta.create_gate("fibonacci_gate", |meta| {
            let s = meta.query_selector(s);
            let c = meta.query_advice(col_c, Rotation::cur());
            let d = meta.query_advice(col_d, Rotation::cur());
            let e = meta.query_advice(col_e, Rotation::cur());
            vec![s * (c + d - e)]
        });

        meta.lookup(|meta| {
            let s = meta.query_selector(s);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table[0]),
                (s.clone() * rhs, xor_table[1]),
                (s * out, xor_table[2]),
            ]
        });

        FibonacciConfig {
            advice: [col_a, col_b, col_c, col_d, col_e],
            selector: s,
            xor_table,
            instance,
        }
    }

    fn load_table<F: FieldExt>(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..256 {
                    for rhs in 0..256 {
                        table.assign_cell(
                            || "xor table lhs",
                            self.xor_table[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "xot table rhs",
                            self.xor_table[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "xor table lhs ^ rhs",
                            self.xor_table[2],
                            idx,
                            || Value::known(F::from(lhs ^ rhs)),
                        )?;
                        idx += 1;
                    }
                }
                Ok(())
            },
        )
    }

    pub fn assign<F: FieldExt>(
        &self,
        mut layouter: impl Layouter<F>,
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire circuit",
            |mut region| {
                self.selector.enable(&mut region, 0)?;

                let mut a_cell = region.assign_advice_from_instance(
                    || "init a",
                    self.instance,
                    0,
                    self.advice[0],
                    0,
                )?;

                let mut b_cell = region.assign_advice_from_instance(
                    || "init b",
                    self.instance,
                    1,
                    self.advice[1],
                    0,
                )?;

                let c_cell = region.assign_advice(
                    || "init c: a ^ b",
                    self.advice[2],
                    0,
                    || {
                        a_cell.value().and_then(|a| {
                            b_cell.value().map(|b| {
                                let a_val = a.get_lower_32() as u64;
                                let b_val = b.get_lower_32() as u64;
                                F::from(a_val ^ b_val)
                            })
                        })
                    },
                )?;

                let d_cell = region.assign_advice(
                    || "init d: 2",
                    self.advice[3],
                    0,
                    || Value::known(F::from(2))
                )?;

                let e_cell = region.assign_advice(
                    || "init e: (a ^ b) + n",
                    self.advice[4],
                    0,
                    || d_cell.value().copied() + c_cell.value(),
                )?;

                a_cell = b_cell;
                b_cell = e_cell;

                for row in 1..nrows {
                    a_cell.copy_advice(|| "copy b -> a", &mut region, self.advice[0], row)?;
                    b_cell.copy_advice(|| "copy e -> b", &mut region, self.advice[1], row)?;

                    let new_e_cell = {
                        self.selector.enable(&mut region, row)?;

                        let c_cell = region.assign_advice(
                            || "c: a ^ b",
                            self.advice[2],
                            row,
                            || {
                                a_cell.value().and_then(|a| {
                                    b_cell.value().map(|b| {
                                        let a_val = a.get_lower_32() as u64;
                                        let b_val = b.get_lower_32() as u64;
                                        F::from(a_val ^ b_val)
                                    })
                                })
                            },
                        )?;

                        let d_cell = region.assign_advice(
                            || "d: n in 2..row_number",
                            self.advice[3],
                            row,
                            || Value::known(F::from((row + 2) as u64))
                        )?;

                        region.assign_advice(
                            || "e: (a ^ b) + n",
                            self.advice[4],
                            row,
                            || d_cell.value().copied() + c_cell.value(),
                        )?
                    };
                    a_cell = b_cell;
                    b_cell = new_e_cell;
                }

                Ok(b_cell)
            },
        )
    }

    pub fn expose_public<F: FieldExt>(
        &self,
        mut layouter: impl Layouter<F>,
        cell: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.instance, row)
    }
}

#[derive(Default)]
struct FibonacciCircuit<F>(PhantomData<F>);

impl<F: FieldExt> Circuit<F> for FibonacciCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FibonacciConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load_table(layouter.namespace(|| "lookup table"))?;
        let out_cell = config.assign(layouter.namespace(|| "entire table"), 11)?;
        config.expose_public(layouter.namespace(|| "out"), out_cell, 2)?;

        Ok(())
    }
}

fn main() {
    let k = 17;

    let a = Fp::from(1); // F[0]
    let b = Fp::from(1); // F[1]
    let out = Fp::from(65); // F[12]

    let circuit = FibonacciCircuit(PhantomData);

    let public_input = vec![a, b, out];

    let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    prover.assert_satisfied();
}
