extern crate halo2;
use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, SimpleFloorPlanner},
    dev::CircuitGates,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

trait NumericInstructions<F: FieldExt>: Chip<F> {
    type Num;

    fn load_private(&self, layouter: impl Layouter<F>, a: Option<F>) -> Result<Self::Num, Error>;

    fn load_constant(&self, layouter: impl Layouter<F>, constant: F) -> Result<Self::Num, Error>;
    fn load_public(&self, layouter: impl Layouter<F>, row: usize) -> Result<Self::Num, Error>;

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
    ) -> <Self as Chip<F>>::Config {
        // enable equality because we will constraint it later on with another
        // cell
        meta.enable_equality(instance.into());
        meta.enable_constant(constant);
        for column in &advices {
            meta.enable_equality((*column).into());
        }
        let smul = meta.selector();
        let sadd = meta.selector();
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

        FieldConfig {
            advices: advices,
            instance: instance,
            constant: constant,
            smul: smul,
            sadd: sadd,
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
                    || a.value.ok_or(Error::SynthesisError),
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
                    || a.value.ok_or(Error::SynthesisError),
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
}

// storing the private variables here
#[derive(Default)]
struct MyCircuit<F: FieldExt> {
    constant: F,
    a: Option<F>,
    b: Option<F>,
    fail: bool,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
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
        FieldChip::configure(meta, advice, instance, constant)
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

        // This works fine when using the same variable
        let bb = field_chip.add(layouter.namespace(|| "2b"), b.clone(), b.clone())?;
        let aa = field_chip.add(layouter.namespace(|| "2a"), a.clone(), a.clone())?;
        // This one not when using two different cells
        if self.fail {
            let ab = field_chip.add(layouter.namespace(|| "a+b"), a.clone(), b.clone())?;
        }

        // a^2 + b^2 + constant = c^2
        //let bsquare = field_chip.mul(layouter.namespace(|| "b^2"), b.clone(), b.clone())?;
        //let asquare = field_chip.mul(layouter.namespace(|| "a^2"), a.clone(), a.clone())?;

        //let ab2 = field_chip.add(layouter.namespace(|| "a^2+b^2"), asquare, bsquare)?;
        //let ab2const = field_chip.add(layouter.namespace(|| "a2 + b2 + const"), ab2, constant)?;
        //let c2 = field_chip.add(layouter.namespace(|| "c^2"), c.clone(), c)?;
        //// TODO can we do it better ? would be nice to have
        //// layouter.constrain_equal instead of spawning a region just for this?
        //layouter.namespace(|| "check equal").assign_region(
        //|| "check",
        //|mut region| {
        //let lhs = region.assign_advice(
        //|| "lhs",
        //field_chip.config().advices[0],
        //0,
        //|| ab2const.value.ok_or(Error::SynthesisError),
        //)?;
        //let rhs = region.assign_advice(
        //|| "rhs",
        //field_chip.config().advices[1],
        //0,
        //|| c2.value.ok_or(Error::SynthesisError),
        //)?;

        //region.constrain_equal(lhs, rhs)
        //},
        /*)?;*/
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use halo2::{dev::MockProver, pasta::Fp};
    #[test]
    fn pythagorean() {
        let k = 10;

        // a^2 + b^2 + k = c^2 ->
        // 2^2 + 3^2 + 3 = 4^2
        let constant = Fp::from(3);
        let a = Fp::from(2);
        let b = Fp::from(3);
        let input = Fp::from(4);

        let circuit = MyCircuit {
            constant,
            a: Some(a),
            b: Some(b),
            fail: true,
        };
        let gates = CircuitGates::collect::<Fp, MyCircuit<Fp>>();
        println!("{}", gates);
        let mut public_inputs = vec![input];
        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
