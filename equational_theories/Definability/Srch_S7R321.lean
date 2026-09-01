import equational_theories.Definability.Srch_S7R321_data

/-!
# A searched exact-automorphism class on `Fin 7`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 7`; the searching is in `Definability/Certs/Srch7R321T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S7R321

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S7R321

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch7R321 {L L' : Law.NatMagmaLaw} (v : Magma.tup7R321)
    (hsrc : @satisfies _ (Fin 7) (Magma.srch7R321 v) L')
    (htgt : ∀ u : Magma.tup7R321, ¬ @satisfies _ (Fin 7) (Magma.srch7R321 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S7R321.E S7R321.Einv S7R321.X S7R321.Xinv S7R321.rep S7R321.tr
    S7R321.z S7R321.st S7R321.hl S7R321.hr S7R321.hxl S7R321.hxr S7R321.htr S7R321.hz S7R321.hst v.1 v.2 hsrc htgt
