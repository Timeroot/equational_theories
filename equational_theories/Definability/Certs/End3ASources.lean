import equational_theories.Definability.ExactEnd3A

/-!
# Term-structural certificate sources: `Magma.end3A`

For each of the following magmas, drawn from the `1` magmas on `Fin 3` whose endomorphism monoid is
exactly the order-`9` monoid of `Magma.endE3A`, the equations it satisfies that no earlier listed
magma does. Together they are the `23` equations that are worth using as the *source* `L'` of a
`Magma.end3A` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `1` members cover them.

This file is generated; see the module docstring of `Definability.ExactEnd3`.
-/

set_option maxHeartbeats 1000000

/-- `23` equations satisfied by `Magma.end3A 0`, and by no earlier member of the cover. -/
theorem end3A_satisfies_0 :
    Satisfies (Magma.end3A 0) [
      46, 307, 308, 309, 310, 311, 312, 4675, 4676, 4677, 4678, 4679, 4680, 4681, 4682, 4683,
      4684, 4685, 4686, 4687, 4688, 4689, 4690
    ] := by decide!
