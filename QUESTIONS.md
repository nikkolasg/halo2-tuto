create_gate: where is the gate enforced ? Where is this polynomial = 0 enforced
anywhere ? 
---> It is enforced everywhere, and it should be valid everywhere depending on
the selector !

------------------------------------------------------------------------------------
Selector:
"""
We need a selector to enable the multiplication gate, so that we aren't placing
    // any constraints on cells where `NumericInstructions::mul` is not being used.
    // This is important when building larger circuits, where columns are used by
    // multiple sets of instructions.
"""
I don't see how a constraint is not being used, in the sense that the polynomial
interpolated at the columns of this selector will just take a different value if
the selector at this row is set or not, i dont see how it "reduces" the work.

------------------------------------------------------------------------------------

Loading constant: 
```
let cell = region.assign_advice_from_constant(
                    || "constant",
                    config.advices[0],
                    0,
                    constant,
                )?;
```
Here's we are assigning a constant into the first advice cell, which is weird
because that cell is already assigned, via load_private 
--> Hypothesis: this is in a new region, so it's a "new row" on the global view

------------------------------------------------------------------------------------

Mul gate assign:
"""
// The inputs we've been given could be located anywhere in the circuit, // but
we can only rely on relative offsets inside this region. So we // assign new
cells inside the region and constrain them to have the // same values as the
inputs.
"""
I don't understand why we are not using the values we loaded during public /
private / constant load methods

--> Because we take "local values". The values/cell loaded as advice or instance
can be re-used anywhere in the circuit. We want the mul gate to operate locally
so we do a copy constraint from the given inputs to local cells and we operate
on local cells.


----------------------------------------------------------------------------------
