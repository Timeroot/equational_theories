import equational_theories.Definability.Srch_S13R82_data

/-!
# A searched exact-automorphism class on `Fin 13`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 13`; the searching is in `Definability/Certs/Srch13R82T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S13R82

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S13R82

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch13R82 {L L' : Law.NatMagmaLaw} (v : Magma.tup13R82)
    (hsrc : @satisfies _ (Fin 13) (Magma.srch13R82 v) L')
    (htgt : ∀ u : Magma.tup13R82, ¬ @satisfies _ (Fin 13) (Magma.srch13R82 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S13R82.E S13R82.Einv S13R82.X S13R82.Xinv S13R82.rep S13R82.tr
    S13R82.z S13R82.st S13R82.hl S13R82.hr S13R82.hxl S13R82.hxr S13R82.htr S13R82.hz S13R82.hst v.1 v.2 hsrc htgt
