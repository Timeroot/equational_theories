import equational_theories.Definability.Srch_S8R58_data

/-!
# A searched exact-automorphism class on `Fin 8`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 8`; the searching is in `Definability/Certs/Srch8R58T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S8R58

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S8R58

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch8R58 {L L' : Law.NatMagmaLaw} (v : Magma.tup8R58)
    (hsrc : @satisfies _ (Fin 8) (Magma.srch8R58 v) L')
    (htgt : ∀ u : Magma.tup8R58, ¬ @satisfies _ (Fin 8) (Magma.srch8R58 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S8R58.E S8R58.Einv S8R58.X S8R58.Xinv S8R58.rep S8R58.tr
    S8R58.z S8R58.st S8R58.hl S8R58.hr S8R58.hxl S8R58.hxr S8R58.htr S8R58.hz S8R58.hst v.1 v.2 hsrc htgt
