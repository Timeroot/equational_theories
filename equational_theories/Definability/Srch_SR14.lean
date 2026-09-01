import equational_theories.Definability.Srch_SR14_data

/-!
# A searched exact-automorphism class on `Fin 6`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 6`; the searching is in `Definability/Certs/SrchR14T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace SR14

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end SR14

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srchR14 {L L' : Law.NatMagmaLaw} (v : Magma.tupR14)
    (hsrc : @satisfies _ (Fin 6) (Magma.srchR14 v) L')
    (htgt : ∀ u : Magma.tupR14, ¬ @satisfies _ (Fin 6) (Magma.srchR14 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK SR14.E SR14.Einv SR14.X SR14.Xinv SR14.rep SR14.tr
    SR14.z SR14.st SR14.hl SR14.hr SR14.hxl SR14.hxr SR14.htr SR14.hz SR14.hst v.1 v.2 hsrc htgt
