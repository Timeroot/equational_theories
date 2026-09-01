import equational_theories.Definability.Srch_S7R306_data

/-!
# A searched exact-automorphism class on `Fin 7`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 7`; the searching is in `Definability/Certs/Srch7R306T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace S7R306

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end S7R306

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srch7R306 {L L' : Law.NatMagmaLaw} (v : Magma.tup7R306)
    (hsrc : @satisfies _ (Fin 7) (Magma.srch7R306 v) L')
    (htgt : ∀ u : Magma.tup7R306, ¬ @satisfies _ (Fin 7) (Magma.srch7R306 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK S7R306.E S7R306.Einv S7R306.X S7R306.Xinv S7R306.rep S7R306.tr
    S7R306.z S7R306.st S7R306.hl S7R306.hr S7R306.hxl S7R306.hxr S7R306.htr S7R306.hz S7R306.hst v.1 v.2 hsrc htgt
