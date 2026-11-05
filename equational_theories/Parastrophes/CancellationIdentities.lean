import equational_theories.Parastrophes.Attributes
import equational_theories.Superposition
import equational_theories.Equations.All

/-! Cancellation proofs on arbitrary carriers. Vampire found the short
equational derivations; every step below is checked by Lean's kernel. -/
namespace Parastrophes.Catalogue
open Law FreeMagma

private theorem cancel690 {G : Type} (M : Magma G) (h : @Equation690 G M)
    (a b c : G) (hc : M.op a b = M.op a c) : b = c := by
  have e4 (x y z : G) : M.op y (M.op x (M.op (M.op z y) x)) = x := (h ..).symm
  have e7 (x : G) : M.op c (M.op x (M.op (M.op a b) x)) = x := by
    rw [hc]; exact e4 x c a
  have e8 (a b c d : G) :
      M.op (M.op a (M.op (M.op b c) a)) (M.op d (M.op a d)) = d :=
    superpose e4 e4
  have e25 (x y z : G) :
      M.op (M.op x (M.op y x)) (M.op z (M.op x z)) = z := superpose e4 e8
  have e36 (x : G) : c = M.op (M.op a (M.op x a)) (M.op c (M.op a b)) :=
    by rw [hc]; exact (e25 a x c).symm
  have e43 : M.op c (M.op a b) = M.op b (M.op a b) := by
    simpa only [e25] using e7 (M.op b (M.op a b))
  have e48 (x : G) : c = M.op (M.op a (M.op x a)) (M.op b (M.op a b)) :=
    superpose e43 e36
  exact (e48 a).trans (e25 a a b) |>.symm

@[parastrophe_result] theorem left_term690_all :
    UniformTermWitness .all Law690 .left (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 1)) := by
  intro G M _ h
  have hh := (@Law690.models_iff G M).mp h
  exact ⟨fun x y => (hh y x x).symm,
    fun x y => cancel690 M hh x _ y (hh (M.op x y) x x).symm⟩

private theorem cancel1353 {G : Type} (M : Magma G) (h : @Equation1353 G M)
    (a b c : G) (hc : M.op a b = M.op a c) : b = c := by
  have e4 (x y z : G) : M.op y (M.op (M.op (M.op z x) y) x) = x := (h ..).symm
  have e7 (x : G) : c = M.op x (M.op (M.op (M.op a b) x) c) := by
    rw [hc]; exact (e4 c x a).symm
  have e9 (a b c d : G) :
      M.op (M.op (M.op (M.op b a) (M.op c d)) a) (M.op a d) = d :=
    superpose e4 e4
  have e30 (x y : G) : M.op (M.op y x) (M.op x y) = y := superpose e4 e9
  have e43 : c = M.op (M.op b a) (M.op a c) := by
    simpa only [e30] using e7 (M.op b a)
  rw [← hc, e30] at e43
  exact e43.symm

@[parastrophe_result] theorem left_term1353_all :
    UniformTermWitness .all Law1353 .left (((Lf 0 ⋆ Lf 1) ⋆ Lf 0) ⋆ Lf 1) := by
  intro G M _ h
  have hh := (@Law1353.models_iff G M).mp h
  exact ⟨fun x y => (hh y x x).symm,
    fun x y => cancel1353 M hh x _ y (hh (M.op x y) x x).symm⟩

end Parastrophes.Catalogue
