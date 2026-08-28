import equational_theories.Definability.Srch_S8R201_data

/-!
# A searched exact-automorphism class on `Fin 8`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 8`; the searching is in `Definability/Certs/Srch8R201T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S8R201

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by native_decide

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end S8R201

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch8R201 {L L' : Law.NatMagmaLaw} (v : Magma.tup8R201)
    (hsrc : @satisfies _ (Fin 8) (Magma.srch8R201 v) L')
    (htgt : ∀ u : Magma.tup8R201, ¬ @satisfies _ (Fin 8) (Magma.srch8R201 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S8R201.E S8R201.Einv S8R201.X S8R201.Xinv S8R201.rep S8R201.tr
    S8R201.z S8R201.st S8R201.hl S8R201.hr S8R201.hxl S8R201.hxr S8R201.htr S8R201.hz S8R201.hst v.1 v.2 hsrc htgt
