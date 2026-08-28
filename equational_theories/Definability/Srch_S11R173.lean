import equational_theories.Definability.Srch_S11R173_data

/-!
# A searched exact-automorphism class on `Fin 11`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 11`; the searching is in `Definability/Certs/Srch11R173T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S11R173

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S11R173

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch11R173 {L L' : Law.NatMagmaLaw} (v : Magma.tup11R173)
    (hsrc : @satisfies _ (Fin 11) (Magma.srch11R173 v) L')
    (htgt : ∀ u : Magma.tup11R173, ¬ @satisfies _ (Fin 11) (Magma.srch11R173 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S11R173.E S11R173.Einv S11R173.X S11R173.Xinv S11R173.rep S11R173.tr
    S11R173.z S11R173.st S11R173.hl S11R173.hr S11R173.hxl S11R173.hxr S11R173.htr S11R173.hz S11R173.hst v.1 v.2 hsrc htgt
