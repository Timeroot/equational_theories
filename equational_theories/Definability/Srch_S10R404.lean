import equational_theories.Definability.Srch_S10R404_data

/-!
# A searched exact-automorphism class on `Fin 10`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 10`; the searching is in `Definability/Certs/Srch10R404T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S10R404

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by native_decide

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end S10R404

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch10R404 {L L' : Law.NatMagmaLaw} (v : Magma.tup10R404)
    (hsrc : @satisfies _ (Fin 10) (Magma.srch10R404 v) L')
    (htgt : ∀ u : Magma.tup10R404, ¬ @satisfies _ (Fin 10) (Magma.srch10R404 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S10R404.E S10R404.Einv S10R404.X S10R404.Xinv S10R404.rep S10R404.tr
    S10R404.z S10R404.st S10R404.hl S10R404.hr S10R404.hxl S10R404.hxr S10R404.htr S10R404.hz S10R404.hst v.1 v.2 hsrc htgt
