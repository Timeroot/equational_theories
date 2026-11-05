import equational_theories.Parastrophes.TranslationLoops
import equational_theories.Superposition

/-!
# An eight-operation exact division image for E695

Let `e(z)=(z*(z*z))*z`. The image identity is
`x=(y*e(z))*((w*(x*w))*y)`. It is equivalent to E1155 together with
`x=x*e(z)`: a cancellation identity and a definable right identity.
It also describes the left-division image of those E1710 models that admit
left division. No finiteness or external certificates are used.
-/
namespace Parastrophes
open Law FreeMagma

namespace Eq695Image

def unit {G : Type*} (M : Magma G) (z : G) : G := M.op (M.op z (M.op z z)) z

def Basis {G : Type} (M : Magma G) : Prop :=
  @Equation1155 G M ∧ ∀ x z, M.op x (unit M z) = x

private theorem forces_unit {G : Type} (M : Magma G) (e : G → G)
    (he : ∀ z, e z = M.op (M.op z (M.op z z)) z)
    (h : ∀ x y z w, M.op (M.op y (e z)) (M.op (M.op w (M.op x w)) y) = x) :
    ∀ x z, M.op x (e z) = x := by
  have e7 (X0 : G) : (e X0) = (M.op (M.op X0 (M.op X0 X0)) X0) :=
    he ..
  have e8 (X0 X1 X2 X3 : G) : (M.op (M.op X1 (e X2)) (M.op (M.op X3 (M.op X0 X3)) X1)) = X0 :=
    h ..
  have e11 (X0 X1 X2 : G) : (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (e X2)) (M.op (M.op X0 (e X0)) X1)) :=
    superpose e7 e8
  have e12 (X0 X1 X2 X3 X4 X5 : G) : (M.op X4 (e X5)) = (M.op (M.op X1 (e X2)) (M.op (M.op (M.op (M.op X3 (M.op X0 X3)) X4) X0) X1)) :=
    superpose e8 e8
  have e13 (X0 X1 : G) : (M.op (M.op X0 (e X1)) (e X0)) = X0 :=
    superpose e7 e8
  have e31 (X0 X1 : G) : (M.op X0 (M.op X0 X0)) = (M.op (M.op (e X0) (e X1)) X0) :=
    superpose e13 e11
  have e35 (X0 X1 X2 X3 X4 : G) : (M.op (M.op X3 (e X4)) (M.op (M.op (M.op X0 (e X1)) (M.op (M.op X2 (e X2)) X0)) X3)) = X2 :=
    superpose e11 e8
  have e43 (X0 X1 : G) : (e X0) = (M.op (M.op (M.op (e X0) (e X1)) X0) X0) :=
    superpose e31 e7
  have e117 (X0 X1 X2 : G) : (M.op X0 (e X1)) = (M.op X0 (e X2)) :=
    superpose e12 e12
  have e206 (X0 X1 X2 : G) : (M.op (M.op X0 (e X1)) (e X2)) = X0 :=
    superpose e117 e13
  have e699 (X0 X1 X2 X3 X4 : G) : (M.op (M.op X1 (e X2)) (M.op (M.op (e (e X0)) (M.op (M.op X4 (e X4)) (M.op (M.op (e (e X0)) (e X3)) (e X0)))) X1)) = X4 :=
    superpose e43 e35
  have e774 (X0 X1 X2 X4 : G) : (M.op (M.op X1 (e X2)) (M.op (M.op (e (e X0)) (M.op (M.op X4 (e X4)) (e (e X0)))) X1)) = X4 :=
    superpose e206 e699
  have e788 (X4 : G) : (M.op X4 (e X4)) = X4 :=
    superpose e8 e774
  exact fun x z => (e117 x z x).trans (e788 x)

/-- The cancellation part alone forces left bijectivity. -/
private theorem leftQuasigroup {G : Type} (M : Magma G) (h : @Equation1155 G M) :
    IsSideQuasigroup .left M := by
  have e6 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 (M.op X0 X2)) X1)) = X0 :=
    mod_symm (h ..)
  have e11 (X0 X1 X3 : G) : (M.op X3 (M.op X0 X3)) = (M.op X1 (M.op X0 X1)) :=
    superpose e6 e6
  have e12 (X0 X1 X2 X3 : G) : (M.op (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X3 X2))) X0) = X3 :=
    superpose e6 e6
  have e170 (X0 X1 X2 : G) : (M.op (M.op X0 (M.op (M.op X1 X2) X0)) X1) = X2 :=
    superpose e11 e12
  intro y
  refine ⟨?_, fun x => ⟨_, (h x y y).symm⟩⟩
  intro a b hab
  have h1 := e170 y y a
  have h2 := e170 y y b
  rw [hab] at h1
  exact h1.symm.trans h2

end Eq695Image

/-- E101161666 in the canonical extended numbering. -/
def leftImage695 : NatMagmaLaw :=
  ⟨Lf 0, (Lf 1 ⋆ ((Lf 2 ⋆ (Lf 2 ⋆ Lf 2)) ⋆ Lf 2)) ⋆
    ((Lf 3 ⋆ (Lf 0 ⋆ Lf 3)) ⋆ Lf 1)⟩

theorem leftImage695_iff {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage695 ↔ ∀ x y z w,
      x = M.op (M.op y (Eq695Image.unit M z)) (M.op (M.op w (M.op x w)) y) := by
  constructor
  · intro h x y z w
    exact h (fun n => if n = 0 then x else if n = 1 then y else if n = 2 then z else w)
  · intro h v
    exact h (v 0) (v 1) (v 2) (v 3)

namespace Eq695Image

theorem iff_basis {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage695 ↔ Basis M := by
  rw [leftImage695_iff]
  constructor
  · intro h
    have hu := forces_unit M (unit M) (fun _ => rfl) (fun x y z w => (h x y z w).symm)
    refine ⟨?_, hu⟩
    intro x y z
    simpa only [hu] using h x y y z
  · rintro ⟨h, hu⟩ x y z w
    simpa only [hu] using h x y w

private theorem forward_h {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1710 G M) :
    @Equation1155 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op (M.op X1 X0) (M.op (M.op X2 X2) X1)) = X0 :=
    mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 :=
    hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 :=
    hd.2 ..
  have e11 : sK0 ≠ (D.op sK1 (D.op (D.op sK2 (D.op sK0 sK2)) sK1)) :=
    mod_symm hn
  have e12 (X0 X1 X2 : G) : (D.op X1 X0) = (M.op X0 (M.op (M.op X2 X2) X1)) :=
    superpose e9 e8
  have e20 (X0 X1 X2 : G) : (D.op (M.op (M.op X1 X1) X0) X2) = (M.op X2 X0) :=
    superpose e8 e12
  have e26 (X0 X1 X2 : G) : (M.op (M.op X2 X2) X0) = (D.op X1 (D.op X0 X1)) :=
    superpose e12 e10
  have e434 (X0 : G) : sK0 ≠ (D.op sK1 (D.op (M.op (M.op X0 X0) sK0) sK1)) :=
    superpose e26 e11
  have e435 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) :=
    superpose e20 e434
  subsumption e435 e10

private theorem forward_unit {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1710 G M) :
    ∀ x z, D.op x (unit D z) = x := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op (M.op X1 X0) (M.op (M.op X2 X2) X1)) = X0 :=
    mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 :=
    hd.1 ..
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 :=
    hd.2 ..
  have e11 : sK0 ≠ (D.op sK0 (D.op (D.op sK1 (D.op sK1 sK1)) sK1)) :=
    mod_symm hn
  have e12 (X0 X1 X2 : G) : (D.op X1 X0) = (M.op X0 (M.op (M.op X2 X2) X1)) :=
    superpose e9 e8
  have e15 (X0 X1 X2 : G) : (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 :=
    superpose e8 e8
  have e20 (X0 X1 X2 : G) : (D.op (M.op (M.op X1 X1) X0) X2) = (M.op X2 X0) :=
    superpose e8 e12
  have e26 (X0 X1 X2 : G) : (M.op (M.op X2 X2) X0) = (D.op X1 (D.op X0 X1)) :=
    superpose e12 e10
  have e37 (X0 X1 : G) : (M.op X0 X0) = (M.op X1 X1) :=
    superpose e15 e15
  have e73 (X0 X1 : G) : (D.op X1 (M.op X0 X0)) = X1 :=
    superpose e37 e10
  have e433 (X0 : G) : sK0 ≠ (D.op sK0 (D.op (M.op (M.op X0 X0) sK1) sK1)) :=
    superpose e26 e11
  have e434 : sK0 ≠ (D.op sK0 (M.op sK1 sK1)) :=
    superpose e20 e433
  subsumption e434 e73

private theorem backward {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : Basis M) :
    @Equation1710 G D := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e9 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op X2 (M.op X0 X2)) X1)) = X0 :=
    mod_symm (h.1 ..)
  have e10 (X0 X1 : G) : (M.op X0 (M.op (M.op X1 (M.op X1 X1)) X1)) = X0 :=
    mod_symm (h.2 ..)
  have e11 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 :=
    hd.1 ..
  have e12 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 :=
    hd.2 ..
  have e13 : sK0 ≠ (D.op (D.op sK1 sK0) (D.op (D.op sK2 sK2) sK1)) :=
    mod_symm hn
  have e14 (X0 X1 X2 : G) : (M.op X1 (M.op (M.op (D.op X2 X0) X0) X1)) = X2 :=
    superpose e11 e9
  have e16 (X0 X1 X3 : G) : (M.op X3 (M.op X0 X3)) = (M.op X1 (M.op X0 X1)) :=
    superpose e9 e9
  have e17 (X0 X1 X2 : G) : (M.op (D.op (M.op X1 (M.op X2 X1)) X0) X0) = X2 :=
    superpose e11 e9
  have e19 (X0 X1 X2 : G) : (M.op (M.op X2 (M.op X0 X2)) X1) = (D.op X1 X0) :=
    superpose e9 e12
  have e27 (X0 X1 : G) : (M.op (M.op X1 (M.op X1 X1)) X1) = (D.op X0 X0) :=
    superpose e10 e12
  have e30 (X0 X1 : G) : (D.op X0 X0) = (D.op X1 X1) :=
    superpose e19 e27
  have e43 (X0 : G) : sK0 ≠ (D.op (D.op sK1 sK0) (D.op (D.op X0 X0) sK1)) :=
    superpose e30 e13
  have e55 (X0 X1 X2 : G) : (M.op X1 (M.op X0 (M.op (D.op X0 X2) X2))) = X1 :=
    superpose e14 e10
  have e116 (X0 X1 X2 : G) : (M.op X1 X2) = (D.op X2 (M.op X0 (M.op X1 X0))) :=
    superpose e16 e12
  have e164 (X0 X1 X2 X3 : G) : (D.op X3 (D.op (M.op X2 (M.op X0 X2)) X1)) = (M.op (M.op X1 X0) X3) :=
    superpose e17 e19
  have e836 (X0 X1 : G) : sK0 ≠ (D.op (D.op sK1 sK0) (D.op (M.op X0 (M.op X1 (M.op X0 X1))) sK1)) :=
    superpose e116 e43
  have e871 (X0 X1 X2 : G) : sK0 ≠ (D.op (D.op sK1 sK0) (D.op (M.op X0 (M.op (M.op X1 (M.op (D.op X1 X2) X2)) X0)) sK1)) :=
    superpose e55 e836
  have e912 (X1 X2 : G) : sK0 ≠ (M.op (M.op sK1 (M.op X1 (M.op (D.op X1 X2) X2))) (D.op sK1 sK0)) :=
    superpose e164 e871
  have e923 : sK0 ≠ (M.op sK1 (D.op sK1 sK0)) :=
    superpose e55 e912
  subsumption e923 e11

private theorem eq695_to1710 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation695 G M) :
    @Equation1710 G M := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op X0 (M.op (M.op X2 X2) X1))) = X0 :=
    mod_symm (h ..)
  have e10 (X0 X1 : G) : (D.op X0 (M.op X0 X1)) = X1 :=
    hd.2 ..
  have e11 : sK0 ≠ (M.op (M.op sK1 sK0) (M.op (M.op sK2 sK2) sK1)) :=
    mod_symm hn
  have e15 (X0 X1 X2 : G) : (M.op X0 (M.op (M.op X2 X2) X1)) = (D.op X1 X0) :=
    superpose e8 e10
  have e61 : sK0 ≠ (D.op sK1 (M.op sK1 sK0)) :=
    superpose e15 e11
  subsumption e61 e10

private theorem eq1710_to695 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1710 G M) :
    @Equation695 G M := by
  by_contra hn
  simp only [not_forall] at hn
  obtain ⟨sK0, sK1, sK2, hn⟩ := hn
  have e8 (X0 X1 X2 : G) : (M.op (M.op X1 X0) (M.op (M.op X2 X2) X1)) = X0 :=
    mod_symm (h ..)
  have e9 (X0 X1 : G) : (M.op X0 (D.op X0 X1)) = X1 :=
    hd.1 ..
  have e11 : sK0 ≠ (M.op sK1 (M.op sK0 (M.op (M.op sK2 sK2) sK1))) :=
    mod_symm hn
  have e12 (X0 X1 X2 : G) : (M.op X0 (M.op (M.op X2 X2) X1)) = (D.op X1 X0) :=
    superpose e9 e8
  have e29 : sK0 ≠ (M.op sK1 (D.op sK1 sK0)) :=
    superpose e12 e11
  subsumption e29 e9

end Eq695Image

namespace Catalogue

/-- An exact eight-operation left-image characterization for E695. -/
@[parastrophe_result] theorem left_characterizes695_all_long :
    Characterizes .all Law695 .left leftImage695 := by
  apply characterizes_of_division
  · intro G M _ h
    exact Eq695Image.leftQuasigroup M ((Eq695Image.iff_basis M).mp h).1
  · intro G M D _ hd h
    have hs := Eq695Image.eq695_to1710 M D hd ((@Law695.models_iff G M).mp h)
    exact (Eq695Image.iff_basis D).mpr
      ⟨Eq695Image.forward_h M D hd hs, Eq695Image.forward_unit M D hd hs⟩
  · intro G M D _ hd h
    have hs := Eq695Image.backward M D hd ((Eq695Image.iff_basis M).mp h)
    exact (@Law695.models_iff G D).mpr (Eq695Image.eq1710_to695 D M (division_symm hd) hs)

/-- E1710 has the same image among its models admitting left division.
This does not assert left bijectivity for every infinite E1710 model. -/
@[parastrophe_result] theorem left_characterizes1710_all_partial :
    Characterizes .all Law1710 .left leftImage695 := by
  apply characterizes_of_division
  · intro G M _ h
    exact Eq695Image.leftQuasigroup M ((Eq695Image.iff_basis M).mp h).1
  · intro G M D _ hd h
    have hs := (@Law1710.models_iff G M).mp h
    exact (Eq695Image.iff_basis D).mpr
      ⟨Eq695Image.forward_h M D hd hs, Eq695Image.forward_unit M D hd hs⟩
  · intro G M D _ hd h
    exact (@Law1710.models_iff G D).mpr (Eq695Image.backward M D hd ((Eq695Image.iff_basis M).mp h))

/-- The inverse multiplication in this image is the three-operation term
`(x*(y*x))*x`. Its two inverse identities follow from E1155 and cancellation. -/
theorem leftImage695_term_all :
    UniformTermWitness .all leftImage695 .left ((Lf 0 ⋆ (Lf 1 ⋆ Lf 0)) ⋆ Lf 0) := by
  intro G M _ h
  have hh := ((Eq695Image.iff_basis M).mp h).1
  have hq := Eq695Image.leftQuasigroup M hh
  have he (x y : G) := (hh y x x).symm
  constructor
  · exact he
  · intro x y
    exact (hq x).1 (he x (M.op x y))

end Catalogue
end Parastrophes
