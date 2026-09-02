import equational_theories.Definability.Srch_S11R400_data

/-!
# A searched exact-automorphism class on `Fin 11`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 11`; the searching is in `Definability/Certs/Srch11R400T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S11R400

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by native_decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by native_decide

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by native_decide

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by native_decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by native_decide

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by native_decide

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by native_decide

end S11R400

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch11R400 {L L' : Law.NatMagmaLaw} (v : Magma.tup11R400)
    (hsrc : @satisfies _ (Fin 11) (Magma.srch11R400 v) L')
    (htgt : ∀ u : Magma.tup11R400, ¬ @satisfies _ (Fin 11) (Magma.srch11R400 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S11R400.E S11R400.Einv S11R400.X S11R400.Xinv S11R400.rep S11R400.tr
    S11R400.z S11R400.st S11R400.hl S11R400.hr S11R400.hxl S11R400.hxr S11R400.htr S11R400.hz S11R400.hst v.1 v.2 hsrc htgt
