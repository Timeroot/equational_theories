import equational_theories.Definability.Srch_SR9_data

/-!
# A searched exact-automorphism class on `Fin 6`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 6`; the searching is in `Definability/Certs/SrchR9T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace SR9

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end SR9

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srchR9 {L L' : Law.NatMagmaLaw} (v : Magma.tupR9)
    (hsrc : @satisfies _ (Fin 6) (Magma.srchR9 v) L')
    (htgt : ∀ u : Magma.tupR9, ¬ @satisfies _ (Fin 6) (Magma.srchR9 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK SR9.E SR9.Einv SR9.X SR9.Xinv SR9.rep SR9.tr
    SR9.z SR9.st SR9.hl SR9.hr SR9.hxl SR9.hxr SR9.htr SR9.hz SR9.hst v.1 v.2 hsrc htgt
