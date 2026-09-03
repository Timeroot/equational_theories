import equational_theories.Definability.Srch_S4R2_data

/-!
# A searched exact-automorphism class on `Fin 4`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 4`; the searching is in `Definability/Certs/Srch4R2T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S4R2

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S4R2

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch4R2 {L L' : Law.NatMagmaLaw} (v : Magma.tup4R2)
    (hsrc : @satisfies _ (Fin 4) (Magma.srch4R2 v) L')
    (htgt : ∀ u : Magma.tup4R2, ¬ @satisfies _ (Fin 4) (Magma.srch4R2 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S4R2.E S4R2.Einv S4R2.X S4R2.Xinv S4R2.rep S4R2.tr
    S4R2.z S4R2.st S4R2.hl S4R2.hr S4R2.hxl S4R2.hxr S4R2.htr S4R2.hz S4R2.hst v.1 v.2 hsrc htgt
