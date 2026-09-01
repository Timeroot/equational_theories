import equational_theories.Definability.Srch_SR18_data

/-!
# A searched exact-automorphism class on `Fin 6`: the rectangle

The data lemmas -- that the listed permutations are permutations, and that the orbit tables say what
`Magma.transport` needs them to say -- and the one theorem the certificates rest on. Everything here
is `decide` on `Fin 6`; the searching is in `Definability/Certs/SrchR18T*.lean`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace SR18

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide!

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide!

theorem hxl : ∀ j, Function.LeftInverse (Xinv j) (X j) := by decide!

theorem hxr : ∀ j, Function.RightInverse (Xinv j) (X j) := by decide!

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide!

theorem hz : ∀ i, tr (rep i).1 (rep i).2 = (i, z i) := by decide!

theorem hst : ∀ i j, tr (E j (rep i).1) (E j (rep i).2) = (i, st i j) := by decide!

end SR18

/-- **The certificate.** If `L'` has a model in the class and no member of the class satisfies
`L`, then `L` is not structural from `L'`, not even over finite carriers: a structural companion
of a member would have the same automorphism group, hence be a member itself. The source side is one
`Satisfies` and the target side one `Magma.searchY` per equation. -/
theorem not_structuralFromFin_of_srchR18 {L L' : Law.NatMagmaLaw} (v : Magma.tupR18)
    (hsrc : @satisfies _ (Fin 6) (Magma.srchR18 v) L')
    (htgt : ∀ u : Magma.tupR18, ¬ @satisfies _ (Fin 6) (Magma.srchR18 u) L) :
    ¬ L.StructuralFromFin L' :=
  Law.MagmaLaw.not_structuralFromFin_of_tupOK SR18.E SR18.Einv SR18.X SR18.Xinv SR18.rep SR18.tr
    SR18.z SR18.st SR18.hl SR18.hr SR18.hxl SR18.hxr SR18.htr SR18.hz SR18.hst v.1 v.2 hsrc htgt
