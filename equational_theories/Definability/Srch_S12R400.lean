import equational_theories.Definability.Srch_S12R400_data

/-!
# A searched exact-automorphism class on `Fin 12`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 12`; the searching is in `Definability/Certs/Srch12R400T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S12R400

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by native_decide

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end S12R400

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch12R400 {L L' : Law.NatMagmaLaw} (v : Magma.tup12R400)
    (hsrc : @satisfies _ (Fin 12) (Magma.srch12R400 v) L')
    (htgt : ∀ u : Magma.tup12R400, ¬ @satisfies _ (Fin 12) (Magma.srch12R400 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S12R400.E S12R400.Einv S12R400.X S12R400.Xinv S12R400.rep S12R400.tr
    S12R400.z S12R400.st S12R400.hl S12R400.hr S12R400.hxl S12R400.hxr S12R400.htr S12R400.hz S12R400.hst v.1 v.2 hsrc htgt
