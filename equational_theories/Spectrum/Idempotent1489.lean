import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status
import equational_theories.Equations.All
import Mathlib.Tactic

/-! Idempotent E1489 models and gluing along pairwise balanced blocks. -/
namespace Spectrum

structure Idempotent1489 (Q : Type*) where
  op : Q → Q → Q
  idem : ∀ x, op x x = x
  law : ∀ x y, op (op y x) (op y (op x y)) = x

namespace Idempotent1489

@[implicit_reducible] def magma {Q : Type*} (D : Idempotent1489 Q) : Magma Q := ⟨D.op⟩

theorem equation1489 {Q : Type*} (D : Idempotent1489 Q) : @Equation1489 Q D.magma :=
  fun x y => (D.law x y).symm

def transport {Q R : Type*} (D : Idempotent1489 Q) (e : R ≃ Q) : Idempotent1489 R where
  op x y := e.symm (D.op (e x) (e y))
  idem x := by simp [D.idem]
  law x y := by simp [D.law]

noncomputable def ofCard {Q : Type*} [Fintype Q] {n : ℕ}
    (h : Fintype.card Q = n) (D : Idempotent1489 (Fin n)) : Idempotent1489 Q :=
  D.transport (Fintype.equivFinOfCardEq h)

section Gluing
open Classical
variable {X I : Type*} (B : I → Set X) (D : ∀ i, Idempotent1489 (B i))
variable (cover : ∀ x y : X, x ≠ y → ∃! i, x ∈ B i ∧ y ∈ B i)

noncomputable def glueOp (x y : X) : X :=
  if h : ∃ i, x ∈ B i ∧ y ∈ B i then
    ((D h.choose).op ⟨x,h.choose_spec.1⟩ ⟨y,h.choose_spec.2⟩).val
  else x

theorem glueOp_idem (x : X) : glueOp B D x x = x := by
  unfold glueOp
  split
  · simp only [Idempotent1489.idem]
  · rfl

include cover in
theorem glueOp_on (i : I) (x y : B i) :
    glueOp B D x.val y.val = ((D i).op x y).val := by
  have he : ∃ j, x.val ∈ B j ∧ y.val ∈ B j := ⟨i,x.property,y.property⟩
  by_cases hxy : x.val = y.val
  · have heq : x = y := Subtype.ext hxy
    subst y
    rw [glueOp_idem, (D i).idem]
  · have hi : he.choose = i := (cover x.val y.val hxy).unique he.choose_spec
      ⟨x.property,y.property⟩
    simp only [glueOp, dif_pos he]
    have transfer (j : I) (hj : j = i) (hx : x.val ∈ B j) (hy : y.val ∈ B j) :
        ((D j).op ⟨x.val,hx⟩ ⟨y.val,hy⟩).val = ((D i).op x y).val := by
      subst j
      rfl
    exact transfer _ hi _ _

noncomputable def glue : Idempotent1489 X where
  op := glueOp B D
  idem := glueOp_idem B D
  law x y := by
    by_cases he : x = y
    · subst y; simp only [glueOp_idem]
    obtain ⟨i,hi,_⟩ := cover x y he
    let u : B i := ⟨x,hi.1⟩
    let v : B i := ⟨y,hi.2⟩
    change glueOp B D (glueOp B D v.val u.val)
      (glueOp B D v.val (glueOp B D u.val v.val)) = u.val
    simp only [glueOp_on B D cover, (D i).law]

end Gluing
end Idempotent1489
end Spectrum
