import equational_theories.Definability.Srch_S7R305_data

/-!
# A searched exact-automorphism class on `Fin 7`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 7`; the searching is in `Definability/Certs/Srch7R305T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S7R305

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S7R305

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch7R305 {L L' : Law.NatMagmaLaw} (v : Magma.tup7R305)
    (hsrc : @satisfies _ (Fin 7) (Magma.srch7R305 v) L')
    (htgt : ∀ u : Magma.tup7R305, ¬ @satisfies _ (Fin 7) (Magma.srch7R305 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S7R305.E S7R305.Einv S7R305.X S7R305.Xinv S7R305.rep S7R305.tr
    S7R305.z S7R305.st S7R305.hl S7R305.hr S7R305.hxl S7R305.hxr S7R305.htr S7R305.hz S7R305.hst v.1 v.2 hsrc htgt
