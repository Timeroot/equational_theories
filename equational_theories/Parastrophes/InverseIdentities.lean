import equational_theories.Parastrophes.Attributes
import equational_theories.Superposition
import equational_theories.Equations.All

/-! Explicit inverse identities on arbitrary carriers. The equational steps
were found by Vampire and are replayed by Lean's kernel; no solver output is
trusted and no finiteness is used. -/
namespace Parastrophes.Catalogue
open Law FreeMagma

private theorem inverse72 {G : Type} (M : Magma G) (h : @Equation72 G M) :
    ∀ x y, (M.op y (M.op (M.op y x) (M.op y x))) = x := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 : G) : (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op sK1 (M.op (M.op sK1 sK0) (M.op sK1 sK0))) := mod_symm hn
  have e8 (X0 : G) : (M.op X0 X0) = (M.op (M.op X0 X0) X0) := superpose e6 e6
  have e9 (X0 : G) : (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := superpose e8 e6
  have e12 (X0 X1 : G) : (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := superpose e9 e6
  have e29 (X0 X1 : G) : (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X1 := superpose e12 e9
  have e178 (X0 X1 : G) : (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := superpose e6 e29
  have e611 : sK0 ≠ (M.op sK1 (M.op sK1 (M.op sK0 sK0))) := superpose e178 e7
  subsumption e611 e6

/-- E72 supplies both inverse identities with the same fixed term,
even for infinite carriers. -/
@[parastrophe_result] theorem left_term72_all_inverse :
    UniformTermWitness .all Law72 .left (Lf 0 ⋆ (Lf 1 ⋆ Lf 1)) := by
  intro G M _ h
  have hh := (@Law72.models_iff G M).mp h
  exact ⟨fun x y => (hh y x).symm, fun x y => inverse72 M hh y x⟩

private theorem inverse117 {G : Type} (M : Magma G) (h : @Equation117 G M) :
    ∀ x y, (M.op (M.op (M.op y x) y) (M.op y x)) = x := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 : G) : (M.op X1 (M.op (M.op X0 X1) X0)) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op (M.op (M.op sK1 sK0) sK1) (M.op sK1 sK0)) := mod_symm hn
  have e8 (X0 X1 : G) : (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = X1 := superpose e6 e6
  have e11 : sK0 ≠ sK0 := superpose e8 e7
  subsumption e11 rfl

/-- E117 supplies both inverse identities with the same fixed term,
even for infinite carriers. -/
@[parastrophe_result] theorem left_term117_all_inverse :
    UniformTermWitness .all Law117 .left ((Lf 1 ⋆ Lf 0) ⋆ Lf 1) := by
  intro G M _ h
  have hh := (@Law117.models_iff G M).mp h
  exact ⟨fun x y => (hh y x).symm, fun x y => inverse117 M hh y x⟩

private theorem inverse501 {G : Type} (M : Magma G) (h : @Equation501 G M) :
    ∀ x y, (M.op y (M.op (M.op y x) (M.op (M.op y x) y))) = x := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 : G) : (M.op X1 (M.op X1 (M.op X0 (M.op X0 X1)))) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op sK1 (M.op (M.op sK1 sK0) (M.op (M.op sK1 sK0) sK1))) := mod_symm hn
  have e9 (X0 X1 : G) : (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X0)) = X1 := superpose e6 e6
  have e10 (X0 X1 : G) : (M.op X1 (M.op X0 (M.op X0 X1))) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) := superpose e6 e9
  have e38 : sK0 ≠ (M.op sK1 (M.op sK1 (M.op sK0 (M.op sK0 sK1)))) := superpose e10 e7
  subsumption e38 e6

/-- E501 supplies both inverse identities with the same fixed term,
even for infinite carriers. -/
@[parastrophe_result] theorem left_term501_all_inverse :
    UniformTermWitness .all Law501 .left (Lf 0 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))) := by
  intro G M _ h
  have hh := (@Law501.models_iff G M).mp h
  exact ⟨fun x y => (hh y x).symm, fun x y => inverse501 M hh y x⟩

private theorem inverse703 {G : Type} (M : Magma G) (h : @Equation703 G M) :
    ∀ x y, (M.op y (M.op (M.op (M.op y x) (M.op y x)) (M.op y x))) = x := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 : G) : (M.op X1 (M.op X1 (M.op (M.op X0 X0) X0))) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op sK1 (M.op (M.op (M.op sK1 sK0) (M.op sK1 sK0)) (M.op sK1 sK0))) := mod_symm hn
  have e8 (X0 : G) : (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X0) := superpose e6 e6
  have e9 (X0 : G) : (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) = X0 := superpose e8 e6
  have e11 (X0 X1 : G) : (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op X1 X0)) := superpose e9 e6
  have e28 (X0 X1 X2 : G) : (M.op (M.op X1 X1) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := superpose e11 e6
  have e131 (X0 X1 : G) : sK0 ≠ (M.op sK1 (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op sK1 sK0)))))) := superpose e28 e7
  have e189 : sK0 ≠ (M.op sK1 (M.op sK1 (M.op (M.op sK0 sK0) sK0))) := superpose e28 e131
  subsumption e189 e6

/-- E703 supplies both inverse identities with the same fixed term,
even for infinite carriers. -/
@[parastrophe_result] theorem left_term703_all_inverse :
    UniformTermWitness .all Law703 .left (Lf 0 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) := by
  intro G M _ h
  have hh := (@Law703.models_iff G M).mp h
  exact ⟨fun x y => (hh y x).symm, fun x y => inverse703 M hh y x⟩

private theorem inverse910 {G : Type} (M : Magma G) (h : @Equation910 G M) :
    ∀ x y, (M.op (M.op y (M.op y x)) (M.op y y)) = x := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 : G) : (M.op X1 (M.op (M.op X1 X0) (M.op X1 X1))) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op (M.op sK1 (M.op sK1 sK0)) (M.op sK1 sK1)) := mod_symm hn
  have e8 (X0 X1 : G) : (M.op (M.op X1 X0) (M.op X1 X1)) = (M.op X1 (M.op X0 (M.op X1 X1))) := superpose e6 e6
  have e12 : sK0 ≠ (M.op sK1 (M.op (M.op sK1 sK0) (M.op sK1 sK1))) := superpose e8 e7
  subsumption e12 e6

/-- E910 supplies both inverse identities with the same fixed term,
even for infinite carriers. -/
@[parastrophe_result] theorem left_term910_all_inverse :
    UniformTermWitness .all Law910 .left ((Lf 0 ⋆ Lf 1) ⋆ (Lf 0 ⋆ Lf 0)) := by
  intro G M _ h
  have hh := (@Law910.models_iff G M).mp h
  exact ⟨fun x y => (hh y x).symm, fun x y => inverse910 M hh y x⟩

private theorem inverse916 {G : Type} (M : Magma G) (h : @Equation916 G M) :
    ∀ x y, (M.op (M.op y y) (M.op (M.op y x) (M.op y x))) = x := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e6 (X0 X1 : G) : (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := mod_symm (h ..)
  have e7 : sK0 ≠ (M.op (M.op sK1 sK1) (M.op (M.op sK1 sK0) (M.op sK1 sK0))) := mod_symm hn
  have e8 (X0 : G) : (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := superpose e6 e6
  have e9 (X0 : G) : (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := superpose e8 e8
  have e10 (X0 : G) : (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := superpose e8 e6
  have e11 (X0 X1 : G) : (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := superpose e8 e6
  have e12 (X0 X1 : G) : (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := superpose e8 e6
  have e16 (X0 : G) : (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := superpose e6 e11
  have e18 (X0 : G) : (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := superpose e6 e16
  have e19 (X0 : G) : (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := superpose e8 e18
  have e20 (X0 : G) : (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := superpose e8 e19
  have e21 (X0 X1 : G) : (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := superpose e8 e12
  have e24 (X0 : G) : (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := superpose e12 e11
  have e25 (X0 : G) : (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := superpose e10 e24
  have e26 (X0 X1 : G) : (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := superpose e20 e21
  have e27 (X0 : G) : (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := superpose e8 e20
  have e28 (X0 : G) : (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := superpose e20 e27
  have e37 (X0 X1 : G) : (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := superpose e9 e12
  have e42 (X0 X1 : G) : (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) X0)) := superpose e20 e37
  have e67 (X0 X1 : G) : (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := superpose e25 e6
  have e92 (X0 X1 : G) : (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := superpose e26 e26
  have e177 (X0 X1 X2 : G) : (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op (M.op X2 X2) X1)) := superpose e67 e67
  have e192 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := superpose e67 e20
  have e195 (X0 X1 : G) : (M.op X1 X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X1) := superpose e67 e28
  have e238 (X0 X1 X2 : G) : (M.op X1 X1) = (M.op X2 (M.op (M.op X2 X2) (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) X1)))) := superpose e42 e11
  have e368 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := superpose e26 e192
  have e728 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := superpose e92 e42
  have e1682 (X0 X1 X2 : G) : (M.op X2 X2) = (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1))) X2)))) := superpose e177 e238
  have e1814 (X0 X1 X2 : G) : (M.op X2 X2) = (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) (M.op X1 (M.op X1 X1))) X2)))) := superpose e728 e1682
  have e1869 (X0 X1 X2 : G) : (M.op X2 X2) = (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X1 X2)))) := superpose e20 e1814
  have e3312 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op X1 (M.op X1 X1)) X0) (M.op (M.op X1 (M.op X1 X1)) X0)) := superpose e238 e1869
  have e3453 (X0 X1 : G) : (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X0)) (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X0))) := superpose e1869 e195
  have e3461 (X0 X1 : G) : (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0))) := superpose e8 e3453
  have e3563 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0))) := superpose e3312 e3461
  have e3595 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := superpose e368 e3563
  have e3932 : sK0 ≠ sK0 := superpose e3595 e7
  subsumption e3932 rfl

/-- E916 supplies both inverse identities with the same fixed term,
even for infinite carriers. -/
@[parastrophe_result] theorem left_term916_all_inverse :
    UniformTermWitness .all Law916 .left ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 1)) := by
  intro G M _ h
  have hh := (@Law916.models_iff G M).mp h
  exact ⟨fun x y => (hh y x).symm, fun x y => inverse916 M hh y x⟩

/-- E1525 also supplies its finite division term on arbitrary carriers.
The square map commutes with multiplication in the form derived below. -/
@[parastrophe_result] theorem left_term1525_all_inverse :
    UniformTermWitness .all Law1525 .left
      (((Lf 0 ⋆ Lf 0) ⋆ Lf 1) ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 1)) := by
  intro G M _ hM
  have h := (@Law1525.models_iff G M).mp hM
  have e6 (X0 X1 : G) : (M.op (M.op X1 X1) (M.op X1 (M.op X0 X0))) = X0 := mod_symm (h ..)
  have e17 (X0 X1 : G) : (M.op X0 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X1))) = X1 := superpose e6 e6
  have e18 (X0 X1 : G) : (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X1 X0)) := superpose e6 e6
  have e27 (X0 X1 X2 : G) : (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X2 X2) (M.op X2 X1)) := superpose e18 e18
  have e35 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op X2 X2))) = X2 := superpose e18 e17
  have e36 (X0 X1 : G) : (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) = X1 := superpose e18 e6
  have e39 (X0 X1 X2 : G) : (M.op X1 X1) = (M.op (M.op X2 X2) (M.op X2 (M.op (M.op X0 X0) (M.op X0 X1)))) := superpose e18 e6
  have e214 (X0 X1 : G) : (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1))) (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X0 X0)) := superpose e39 e39
  have e305 (X0 X1 : G) : (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X1 X1) (M.op X0 X0)) := superpose e6 e214
  have e784 (X0 X1 : G) : (M.op X0 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) = X1 := superpose e305 e35
  exact ⟨e784, e36⟩

end Parastrophes.Catalogue
