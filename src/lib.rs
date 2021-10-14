extern crate halo2;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, SimpleFloorPlanner},
    dev::CircuitGates,
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector, TableColumn,
    },
    poly::Rotation,
};
use std::marker::PhantomData;

trait NumericInstructions<F: FieldExt>: Chip<F> {
    type Num;

    fn load_private(&self, layouter: impl Layouter<F>, a: Option<F>) -> Result<Self::Num, Error>;
    fn load_constant(&self, layouter: impl Layouter<F>, constant: F) -> Result<Self::Num, Error>;
    fn load_public(&self, layouter: impl Layouter<F>, row: usize) -> Result<Self::Num, Error>;
    fn load_xor_table(&self, layouter: impl Layouter<F>) -> Result<(), Error>;

    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;

    fn mul(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
    fn add(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    fn xor(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
}

// Do the circuit: a^2 + b^2 + q = c^2 with c public input (instance) and a and b and q
// are the witness
// Any constant is loaded into the first advice column
// The total matrix will look stg like:
// advice[0] advice[1] fixed s_mul s_add instance
//                                        c
// a
// b
//                      q
// a          a              1                  <---- mul gate
// a^2
// b          b              1                   <---- mul gate
// b^2
// a^2        b^2      q            1            <---- add gate
// c        c
// c^2                       1                   <---- mul gate
struct FieldChip<F: FieldExt> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Chip<F> for FieldChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
#[derive(Clone, Debug)]
struct FieldConfig {
    // witness columns: a and b
    advices: [Column<Advice>; 2],
    // public inputs columns
    instance: Column<Instance>,
    smul: Selector,
    sadd: Selector,
    constant: Column<Fixed>,

    // lookup is only relevant when this selector is set
    stable: Selector,
    // size of the bits we are considering - directly impacting size of the
    // table
    xor_bitlength: usize,
    // XOR table with three columns: a XOR b = c
    xor_table: [TableColumn; 3],
    // the witness of the XOR'd value that we must give and then we can verify
    // if the triplet a XOR b = xord is inside the table columns
    xord: Column<Advice>,
}

impl<F: FieldExt> FieldChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
    fn configure(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; 2],
        instance: Column<Instance>,
        constant: Column<Fixed>,
        xor_size: usize,
        xor_table: [TableColumn; 3],
        xord: Column<Advice>,
    ) -> <Self as Chip<F>>::Config {
        // enable equality because we will constraint it later on with another
        // cell
        meta.enable_equality(instance.into());
        meta.enable_constant(constant);
        for column in &advices {
            meta.enable_equality((*column).into());
        }
        meta.enable_equality(xord.into());

        let smul = meta.selector();
        let sadd = meta.selector();
        let stable = meta.complex_selector();

        meta.create_gate("mul", |meta| {
            let lhs = meta.query_advice(advices[0], Rotation::cur());
            let rhs = meta.query_advice(advices[1], Rotation::cur());
            let out = meta.query_advice(advices[0], Rotation::next());
            let sel = meta.query_selector(smul);
            vec![sel * (lhs * rhs - out)]
        });

        meta.create_gate("add", |meta| {
            let lhs = meta.query_advice(advices[0], Rotation::cur());
            let rhs = meta.query_advice(advices[1], Rotation::cur());
            let out = meta.query_advice(advices[0], Rotation::next());
            let sel = meta.query_selector(sadd);
            vec![sel * ((lhs + rhs) - out)]
        });

        meta.lookup(|meta| {
            let a = meta.query_advice(advices[0], Rotation::cur());
            let b = meta.query_advice(advices[1], Rotation::cur());
            let xored = meta.query_advice(xord, Rotation::cur());
            let sel = meta.query_selector(stable);
            vec![
                (sel.clone() * a, xor_table[0]),
                (sel.clone() * b, xor_table[1]),
                (sel.clone() * xored, xor_table[2]),
            ]
        });

        FieldConfig {
            advices: advices,
            instance: instance,
            constant: constant,
            smul: smul,
            sadd: sadd,
            stable: stable,
            xor_bitlength: xor_size,
            xor_table: xor_table,
            xord: xord,
        }
    }
}

#[derive(Clone)]
struct Number<F: FieldExt> {
    cell: Cell,
    value: Option<F>,
}
impl<F: FieldExt> NumericInstructions<F> for FieldChip<F> {
    type Num = Number<F>;

    fn load_xor_table(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let config = self.config();
        let bits = config.xor_bitlength;
        let max = 1 << bits;
        layouter.assign_table(
            || "xor table",
            |mut table| {
                let mut row = 0;
                for i in 0..max {
                    for j in 0..max {
                        let xor = i ^ j;
                        table.assign_cell(
                            || "table_a",
                            config.xor_table[0],
                            row,
                            || Ok(F::from(i)),
                        )?;
                        table.assign_cell(
                            || "table_b",
                            config.xor_table[1],
                            row,
                            || Ok(F::from(j)),
                        )?;
                        table.assign_cell(
                            || "table_xor",
                            config.xor_table[2],
                            row,
                            || Ok(F::from(xor)),
                        )?;
                        row += 1;
                    }
                }
                Ok(())
            },
        )
    }
    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Option<F>,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        let mut num = None;
        layouter.assign_region(
            || "load private",
            |mut region| {
                let cell = region.assign_advice(
                    || "private_input",
                    config.advices[0],
                    0,
                    || value.ok_or(Error::SynthesisError),
                )?;
                num = Some(Number { cell: cell, value });
                Ok(())
            },
        )?;
        Ok(num.unwrap())
    }

    fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        constant: F,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        let mut num = None;
        layouter.assign_region(
            || "load constant",
            |mut region| {
                let cell = region.assign_advice_from_constant(
                    || "constant",
                    config.advices[0],
                    0,
                    constant,
                )?;
                num = Some(Number {
                    cell: cell,
                    value: Some(constant),
                });
                Ok(())
            },
        )?;
        Ok(num.unwrap())
    }

    fn load_public(&self, mut layouter: impl Layouter<F>, row: usize) -> Result<Self::Num, Error> {
        let config = self.config();
        let mut num = None;
        layouter.assign_region(
            || "load public",
            |mut region| {
                let cell = region.assign_advice_from_instance(
                    || "instance",
                    config.instance,
                    row,
                    config.advices[0],
                    0,
                )?;
                num = Some(Number {
                    cell: cell.0,
                    value: cell.1,
                });
                Ok(())
            },
        )?;
        Ok(num.unwrap())
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();
        // Constrains a [`Cell`] to equal an instance column's row value at an
        // absolute position.
        // This
        layouter.constrain_instance(num.cell, config.instance, row)
    }

    fn add(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        let mut out = None;
        layouter.assign_region(
            || "add",
            |mut region| {
                config.sadd.enable(&mut region, 0)?;
                let lhs = region.assign_advice(
                    || "lhs",
                    config.advices[0],
                    0,
                    || a.value.ok_or(Error::SynthesisError),
                )?;
                let rhs = region.assign_advice(
                    || "rhs",
                    config.advices[1],
                    0,
                    || b.value.ok_or(Error::SynthesisError),
                )?;
                region.constrain_equal(a.cell, lhs)?;
                region.constrain_equal(b.cell, rhs)?;
                let res = a.value.and_then(|a| b.value.map(|b| a + b));
                let cell = region.assign_advice(
                    || "lhs + rhs",
                    config.advices[0],
                    1, // OFFSET
                    || res.ok_or(Error::SynthesisError),
                )?;
                out = Some(Number {
                    value: res,
                    cell: cell,
                });
                Ok(())
            },
        )?;
        Ok(out.unwrap())
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        let mut out = None;
        layouter.assign_region(
            || "mul",
            |mut region| {
                config.smul.enable(&mut region, 0)?;
                let lhs = region.assign_advice(
                    || "lhs",
                    config.advices[0],
                    0,
                    || a.value.ok_or(Error::SynthesisError),
                )?;
                let rhs = region.assign_advice(
                    || "rhs",
                    config.advices[1],
                    0,
                    || b.value.ok_or(Error::SynthesisError),
                )?;
                region.constrain_equal(a.cell, lhs)?;
                region.constrain_equal(b.cell, rhs)?;
                let res = a.value.and_then(|a| b.value.map(|b| a * b));
                let cell = region.assign_advice(
                    || "lhs * rhs",
                    config.advices[0],
                    1, // OFFSET !
                    || res.ok_or(Error::SynthesisError),
                )?;
                out = Some(Number {
                    value: res,
                    cell: cell,
                });
                Ok(())
            },
        )?;
        Ok(out.unwrap())
    }

    fn xor(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        let mut out = None;
        layouter.assign_region(
            || "mul",
            |mut region| {
                config.stable.enable(&mut region, 0)?;
                let lhs = region.assign_advice(
                    || "xor a",
                    config.advices[0],
                    0,
                    || a.value.ok_or(Error::SynthesisError),
                )?;
                let rhs = region.assign_advice(
                    || "xor b",
                    config.advices[1],
                    0,
                    || b.value.ok_or(Error::SynthesisError),
                )?;
                region.constrain_equal(a.cell, lhs)?;
                region.constrain_equal(b.cell, rhs)?;
                let res = a.value.and_then(|a| {
                    b.value
                        .map(|b| F::from((a.get_lower_32() ^ b.get_lower_32()) as u64))
                });
                let xord = region.assign_advice(
                    || "xor-d",
                    config.xord,
                    0, // Could use offset as well - but here we use a new column
                    || res.ok_or(Error::SynthesisError),
                )?;
                out = Some(Number {
                    value: res,
                    cell: xord,
                });
                Ok(())
            },
        )?;
        Ok(out.unwrap())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use halo2::{dev::MockProver, pasta::Fp};
    #[test]
    fn pasta_bits() {
        let exp: u32 = 13;
        let a = Fp::from(exp as u64);
        let got = a.get_lower_32();
        assert_eq!(exp, got);
    }
    #[test]
    fn pythagorean() {
        // storing the private variables here
        #[derive(Default)]
        struct Pythagore<F: FieldExt> {
            constant: F,
            a: Option<F>,
            b: Option<F>,
        }

        impl<F: FieldExt> Circuit<F> for Pythagore<F> {
            // Since we are using a single chip for everything, we can just reuse its config.
            type Config = FieldConfig;
            type FloorPlanner = SimpleFloorPlanner;
            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let advice = [meta.advice_column(), meta.advice_column()];
                let instance = meta.instance_column();
                let constant = meta.fixed_column();

                let xor_table = [
                    meta.lookup_table_column(),
                    meta.lookup_table_column(),
                    meta.lookup_table_column(),
                ];
                let xord = meta.advice_column();
                let bitsize = 2;
                FieldChip::configure(meta, advice, instance, constant, bitsize, xor_table, xord)
            }
            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let field_chip = FieldChip::<F>::construct(config);
                let a = field_chip.load_private(layouter.namespace(|| "load a"), self.a)?;
                let b = field_chip.load_private(layouter.namespace(|| "load b"), self.b)?;
                let c = field_chip.load_public(layouter.namespace(|| "load pub c"), 0)?;
                let constant =
                    field_chip.load_constant(layouter.namespace(|| "load const"), self.constant)?;

                // a^2 + b^2 + constant = c^2
                let bsquare = field_chip.mul(layouter.namespace(|| "b^2"), b.clone(), b.clone())?;
                let asquare = field_chip.mul(layouter.namespace(|| "a^2"), a.clone(), a.clone())?;

                let ab2 = field_chip.add(layouter.namespace(|| "a^2+b^2"), asquare, bsquare)?;
                let ab2const = field_chip.add(
                    layouter.namespace(|| "a2 + b2 + const"),
                    ab2.clone(),
                    constant,
                )?;
                let c2 = field_chip.mul(layouter.namespace(|| "c^2"), c.clone(), c.clone())?;
                //// TODO can we do it better ? would be nice to have
                //// layouter.constrain_equal instead of spawning a region just for this?
                layouter.namespace(|| "check equal").assign_region(
                    || "check",
                    |mut region| {
                        let lhs = region.assign_advice(
                            || "lhs",
                            field_chip.config().advices[0],
                            0,
                            || ab2const.value.ok_or(Error::SynthesisError),
                        )?;
                        let rhs = region.assign_advice(
                            || "rhs",
                            field_chip.config().advices[1],
                            0,
                            || c2.value.ok_or(Error::SynthesisError),
                        )?;
                        region.constrain_equal(ab2const.cell, lhs)?;
                        region.constrain_equal(c2.cell, rhs)?;
                        region.constrain_equal(lhs, rhs)
                    },
                )?;

                let _ = field_chip.xor(layouter.namespace(|| "a xor b"), a.clone(), b.clone())?;
                Ok(())
            }
        }

        let k = 10;
        // a^2 + b^2 + k = c^2 ->
        // 2^2 + 3^2 + 3 = 4^2
        let constant = Fp::from(3);
        let a = Fp::from(2);
        let b = Fp::from(3);
        let input = Fp::from(4);

        let circuit = Pythagore {
            constant,
            a: Some(a),
            b: Some(b),
        };
        let gates = CircuitGates::collect::<Fp, Pythagore<Fp>>();
        println!("{}", gates);
        let public_inputs = vec![input];
        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        // bad inputs
        let public_inputs = vec![input + Fp::from(1)];
        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
