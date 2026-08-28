import equational_theories.Definability.ExactEnd6AD

/-!
# Term-structural certificate sources: `Magma.end6AD`

For each of the following magmas, drawn from the `12` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`141` monoid of `Magma.endE6AD`, the equations it satisfies that no earlier listed
magma does. Together they are the `11` equations that are worth using as the *source* `L'` of a
`Magma.end6AD` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `6` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `4` equations satisfied by `Magma.end6AD 8`, and by no earlier member of the cover. -/
theorem end6AD_satisfies_0 :
    Satisfies (Magma.end6AD 8) [
      647, 2068, 2688, 2880
    ] := by decide!

/-- `3` equations satisfied by `Magma.end6AD 11`, and by no earlier member of the cover. -/
theorem end6AD_satisfies_1 :
    Satisfies (Magma.end6AD 11) [
      1543, 2949, 2964
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AD 0`, and by no earlier member of the cover. -/
theorem end6AD_satisfies_2 :
    Satisfies (Magma.end6AD 0) [
      3317
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AD 2`, and by no earlier member of the cover. -/
theorem end6AD_satisfies_3 :
    Satisfies (Magma.end6AD 2) [
      4209
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AD 3`, and by no earlier member of the cover. -/
theorem end6AD_satisfies_4 :
    Satisfies (Magma.end6AD 3) [
      1244
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AD 5`, and by no earlier member of the cover. -/
theorem end6AD_satisfies_5 :
    Satisfies (Magma.end6AD 5) [
      2259
    ] := by decide!
