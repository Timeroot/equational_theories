import equational_theories.Definability.Srch_SR7_data

/-!
# A searched exact-automorphism class on `Fin 6`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 6`; the searching is in `Definability/Certs/SrchR7T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace SR7

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end SR7

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srchR7 {L L' : Law.NatMagmaLaw} (v : Magma.tupR7)
    (hsrc : @satisfies _ (Fin 6) (Magma.srchR7 v) L')
    (htgt : ∀ u : Magma.tupR7, ¬ @satisfies _ (Fin 6) (Magma.srchR7 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK SR7.E SR7.Einv SR7.X SR7.Xinv SR7.rep SR7.tr
    SR7.z SR7.st SR7.hl SR7.hr SR7.hxl SR7.hxr SR7.htr SR7.hz SR7.hst v.1 v.2 hsrc htgt
