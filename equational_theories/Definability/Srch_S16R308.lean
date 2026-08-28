import equational_theories.Definability.Srch_S16R308_data

/-!
# A searched exact-automorphism class on `Fin 16`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 16`; the searching is in `Definability/Certs/Srch16R308T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S16R308

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by native_decide

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end S16R308

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch16R308 {L L' : Law.NatMagmaLaw} (v : Magma.tup16R308)
    (hsrc : @satisfies _ (Fin 16) (Magma.srch16R308 v) L')
    (htgt : ∀ u : Magma.tup16R308, ¬ @satisfies _ (Fin 16) (Magma.srch16R308 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S16R308.E S16R308.Einv S16R308.X S16R308.Xinv S16R308.rep S16R308.tr
    S16R308.z S16R308.st S16R308.hl S16R308.hr S16R308.hxl S16R308.hxr S16R308.htr S16R308.hz S16R308.hst v.1 v.2 hsrc htgt
