import equational_theories.Definability.Srch_S11R314_data

/-!
# A searched exact-automorphism class on `Fin 11`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 11`; the searching is in `Definability/Certs/Srch11R314T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S11R314

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S11R314

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch11R314 {L L' : Law.NatMagmaLaw} (v : Magma.tup11R314)
    (hsrc : @satisfies _ (Fin 11) (Magma.srch11R314 v) L')
    (htgt : ∀ u : Magma.tup11R314, ¬ @satisfies _ (Fin 11) (Magma.srch11R314 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S11R314.E S11R314.Einv S11R314.X S11R314.Xinv S11R314.rep S11R314.tr
    S11R314.z S11R314.st S11R314.hl S11R314.hr S11R314.hxl S11R314.hxr S11R314.htr S11R314.hz S11R314.hst v.1 v.2 hsrc htgt
