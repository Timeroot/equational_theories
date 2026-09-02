import equational_theories.Definability.Srch_S9R411_data

/-!
# A searched exact-automorphism class on `Fin 9`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 9`; the searching is in `Definability/Certs/Srch9R411T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S9R411

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S9R411

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch9R411 {L L' : Law.NatMagmaLaw} (v : Magma.tup9R411)
    (hsrc : @satisfies _ (Fin 9) (Magma.srch9R411 v) L')
    (htgt : ∀ u : Magma.tup9R411, ¬ @satisfies _ (Fin 9) (Magma.srch9R411 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S9R411.E S9R411.Einv S9R411.X S9R411.Xinv S9R411.rep S9R411.tr
    S9R411.z S9R411.st S9R411.hl S9R411.hr S9R411.hxl S9R411.hxr S9R411.htr S9R411.hz S9R411.hst v.1 v.2 hsrc htgt
