import equational_theories.Spectrum.Basic
import Mathlib.Tactic

/-! Idempotent models of two-variable identities, and pairwise balanced gluing.
These constructions are independent of the identity chosen. -/
namespace Spectrum.PBD
open Classical FreeMagma Law

abbrev BinaryLaw := MagmaLaw Bool

abbrev eval {A : Type*} (op : A → A → A) (t : FreeMagma Bool) (x y : A) : A :=
  @evalInMagma Bool A ⟨op⟩ (fun b => if b then y else x) t

structure Model (L : BinaryLaw) (A : Type*) where
  op : A → A → A
  idem : ∀ x, op x x = x
  law : ∀ x y, eval op L.lhs x y = eval op L.rhs x y

namespace Model
variable {L : BinaryLaw} {A C : Type*}

theorem eval_map {op : A → A → A} {op' : C → C → C} (f : A → C)
    (hf : ∀ x y, f (op x y) = op' (f x) (f y)) (t : FreeMagma Bool) (x y : A) :
    f (eval op t x y) = eval op' t (f x) (f y) := by
  induction t with
  | Leaf b => cases b <;> rfl
  | Fork t u ht hu => exact (hf _ _).trans (congrArg₂ op' ht hu)

def transport (M : Model L A) (e : A ≃ C) : Model L C where
  op x y := e (M.op (e.symm x) (e.symm y))
  idem x := by simp [M.idem]
  law x y := by
    have h (t : FreeMagma Bool) := eval_map (op := M.op)
      (op' := fun x y => e (M.op (e.symm x) (e.symm y))) e
      (fun _ _ => by simp) t (e.symm x) (e.symm y)
    simpa only [Equiv.apply_symm_apply] using (h L.lhs).symm.trans
      ((congrArg e (M.law _ _)).trans (h L.rhs))

noncomputable def ofCard [Fintype C] {n : ℕ} (M : Model L (Fin n))
    (hc : Fintype.card C = n) : Model L C :=
  M.transport (Fintype.equivFinOfCardEq hc).symm

def product (M : Model L A) (N : Model L C) : Model L (A × C) where
  op x y := (M.op x.1 y.1, N.op x.2 y.2)
  idem x := Prod.ext (M.idem x.1) (N.idem x.2)
  law x y := by
    apply Prod.ext
    · have h := eval_map (op := fun x y : A × C => (M.op x.1 y.1, N.op x.2 y.2))
        (op' := M.op) Prod.fst (fun _ _ => rfl)
      exact (h _ _ _).trans ((M.law _ _).trans (h _ _ _).symm)
    · have h := eval_map (op := fun x y : A × C => (M.op x.1 y.1, N.op x.2 y.2))
        (op' := N.op) Prod.snd (fun _ _ => rfl)
      exact (h _ _ _).trans ((N.law _ _).trans (h _ _ _).symm)

noncomputable def mul {n m : ℕ} (M : Model L (Fin n)) (N : Model L (Fin m)) :
    Model L (Fin (n*m)) := (M.product N).transport (Fintype.equivFinOfCardEq (by simp))

def empty : Model L (Fin 0) where
  op x _ := x
  idem _ := rfl
  law x := Fin.elim0 x

def one : Model L (Fin 1) where
  op x _ := x
  idem _ := rfl
  law _ _ := Subsingleton.elim _ _

theorem eval_self {op : A → A → A} (hi : ∀ x, op x x = x)
    (t : FreeMagma Bool) (x : A) : eval op t x x = x := by
  induction t with
  | Leaf b => cases b <;> rfl
  | Fork _ _ ht hu => exact (congrArg₂ op ht hu).trans (hi x)

section Gluing
variable {I : Type*} (B : I → Set A) (M : ∀ i, Model L (B i))
variable (cover : ∀ x y : A, x ≠ y → ∃! i, x ∈ B i ∧ y ∈ B i)

noncomputable def glueOp (x y : A) : A :=
  if h : ∃ i, x ∈ B i ∧ y ∈ B i then
    ((M h.choose).op ⟨x,h.choose_spec.1⟩ ⟨y,h.choose_spec.2⟩).val
  else x

theorem glueOp_idem (x : A) : glueOp B M x x = x := by
  unfold glueOp
  split
  · simp only [Model.idem]
  · rfl

include cover in
theorem glueOp_on (i : I) (x y : B i) :
    glueOp B M x.val y.val = ((M i).op x y).val := by
  have he : ∃ j, x.val ∈ B j ∧ y.val ∈ B j := ⟨i,x.property,y.property⟩
  by_cases hxy : x.val = y.val
  · have heq : x = y := Subtype.ext hxy
    subst y
    rw [glueOp_idem, (M i).idem]
  · have hi : he.choose = i := (cover x.val y.val hxy).unique he.choose_spec
      ⟨x.property,y.property⟩
    simp only [glueOp, dif_pos he]
    have transfer (j : I) (hj : j = i) (hx : x.val ∈ B j) (hy : y.val ∈ B j) :
        ((M j).op ⟨x.val,hx⟩ ⟨y.val,hy⟩).val = ((M i).op x y).val := by
      subst j
      rfl
    exact transfer _ hi _ _

noncomputable def glue : Model L A where
  op := glueOp B M
  idem := glueOp_idem B M
  law x y := by
    by_cases he : x = y
    · subst y
      rw [eval_self (glueOp_idem B M), eval_self (glueOp_idem B M)]
    obtain ⟨i,hi,_⟩ := cover x y he
    let u : B i := ⟨x,hi.1⟩
    let v : B i := ⟨y,hi.2⟩
    have h (t : FreeMagma Bool) := eval_map (op := (M i).op)
      (op' := glueOp B M) Subtype.val
      (fun a b => (glueOp_on B M cover i a b).symm) t u v
    exact (h L.lhs).symm.trans ((congrArg Subtype.val ((M i).law u v)).trans (h L.rhs))

end Gluing
end Model
end Spectrum.PBD
