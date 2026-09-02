import equational_theories.Definability.Srch_S9R403_data

/-!
# A searched exact-automorphism class on `Fin 9`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 9`; the searching is in `Definability/Certs/Srch9R403T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S9R403

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S9R403

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch9R403 {L L' : Law.NatMagmaLaw} (v : Magma.tup9R403)
    (hsrc : @satisfies _ (Fin 9) (Magma.srch9R403 v) L')
    (htgt : ∀ u : Magma.tup9R403, ¬ @satisfies _ (Fin 9) (Magma.srch9R403 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S9R403.E S9R403.Einv S9R403.X S9R403.Xinv S9R403.rep S9R403.tr
    S9R403.z S9R403.st S9R403.hl S9R403.hr S9R403.hxl S9R403.hxr S9R403.htr S9R403.hz S9R403.hst v.1 v.2 hsrc htgt
