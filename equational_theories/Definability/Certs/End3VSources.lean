import equational_theories.Definability.ExactEnd3V

/-!
# Term-structural certificate sources: `Magma.end3V`

For each of the following magmas, drawn from the `2` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`6` monoid of `Magma.endE3V`, the equations it satisfies that no earlier listed
magma does. Together they are the `18` equations that are worth using as the *source* `L'` of a
`Magma.end3V` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `2` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `11` equations satisfied by `Magma.end3V 0`, and by no earlier member of the cover. -/
theorem end3V_satisfies_0 :
    Satisfies (Magma.end3V 0) [
      323, 333, 378, 3316, 3512, 3546, 3918, 4291, 4362, 4445, 4636
    ] := by decide!

/-- `7` equations satisfied by `Magma.end3V 1`, and by no earlier member of the cover. -/
theorem end3V_satisfies_1 :
    Satisfies (Magma.end3V 1) [
      377, 3927, 4128, 4321, 4472, 4629, 4673
    ] := by decide!
