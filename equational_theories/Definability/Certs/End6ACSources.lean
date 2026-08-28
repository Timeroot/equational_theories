import equational_theories.Definability.ExactEnd6AC

/-!
# Term-structural certificate sources: `Magma.end6AC`

For each of the following magmas, drawn from the `12` magmas on `Fin 6` whose endomorphism monoid is
exactly the order-`882` monoid of `Magma.endE6AC`, the equations it satisfies that no earlier listed
magma does. Together they are the `21` equations that are worth using as the *source* `L'` of a
`Magma.end6AC` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `5` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd6`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- `8` equations satisfied by `Magma.end6AC 0`, and by no earlier member of the cover. -/
theorem end6AC_satisfies_0 :
    Satisfies (Magma.end6AC 0) [
      379, 3520, 3919, 3926, 3929, 4400, 4437, 4474
    ] := by decide!

/-- `8` equations satisfied by `Magma.end6AC 1`, and by no earlier member of the cover. -/
theorem end6AC_satisfies_1 :
    Satisfies (Magma.end6AC 1) [
      3583, 3587, 3600, 3989, 4006, 4529, 4533, 4546
    ] := by decide!

/-- `2` equations satisfied by `Magma.end6AC 10`, and by no earlier member of the cover. -/
theorem end6AC_satisfies_2 :
    Satisfies (Magma.end6AC 10) [
      3939, 3947
    ] := by decide!

/-- `2` equations satisfied by `Magma.end6AC 11`, and by no earlier member of the cover. -/
theorem end6AC_satisfies_3 :
    Satisfies (Magma.end6AC 11) [
      3515, 3541
    ] := by decide!

/-- `1` equations satisfied by `Magma.end6AC 2`, and by no earlier member of the cover. -/
theorem end6AC_satisfies_4 :
    Satisfies (Magma.end6AC 2) [
      3751
    ] := by decide!
