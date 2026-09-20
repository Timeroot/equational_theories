import equational_theories.Definability.CloneFamilyCounting
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

/-! Matrix-affine clone families in arbitrary finite dimension, with exact
coefficient tests for laws over a finite set of variables. -/

open Matrix FreeMagma Law
open scoped BigOperators

namespace Magma.MatrixFamily

variable {R : Type} [CommRing R] {d k : ℕ}
abbrev V (R : Type) (d : ℕ) := Fin d → R
abbrev M (R : Type) (d : ℕ) := Matrix (Fin d) (Fin d) R
abbrev P (R : Type) (d : ℕ) := M R d × M R d × V R d

def op (p : P R d) (x y : V R d) : V R d := p.1 *ᵥ x + p.2.1 *ᵥ y + p.2.2

def comp (p q r : P R d) : P R d :=
  (p.1 * q.1 + p.2.1 * r.1,
   p.1 * q.2.1 + p.2.1 * r.2.1,
   p.1 *ᵥ q.2.2 + p.2.1 *ᵥ r.2.2 + p.2.2)

theorem op_injective : Function.Injective (op (R := R) (d := d)) := by
  rintro ⟨a, b, c⟩ ⟨e, f, g⟩ h
  have hc : c = g := by simpa [op] using congrFun (congrFun h 0) 0
  have ha : a = e := by
    apply Matrix.ext_of_mulVec_single
    intro j
    simpa [op, hc] using congrFun (congrFun h (Pi.single j 1)) 0
  have hb : b = f := by
    apply Matrix.ext_of_mulVec_single
    intro j
    simpa [op, hc] using congrFun (congrFun h 0) (Pi.single j 1)
  exact Prod.ext ha (Prod.ext hb hc)

theorem op_fst (x y : V R d) : op (1, 0, 0) x y = x := by simp [op]
theorem op_snd (x y : V R d) : op (0, 1, 0) x y = y := by simp [op]
theorem op_comp (p q r : P R d) (x y : V R d) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := by
  simp only [op, comp, add_mulVec, mulVec_add, mulVec_mulVec]
  abel

abbrev C (R : Type) (d k : ℕ) := (Fin k → M R d) × V R d

def coefficients (p : P R d) : FreeMagma (Fin k) → C R d k
  | .Leaf j => (fun i => if i = j then 1 else 0, 0)
  | .Fork a b =>
    let ca := coefficients p a
    let cb := coefficients p b
    (fun i => p.1 * ca.1 i + p.2.1 * cb.1 i,
     p.1 *ᵥ ca.2 + p.2.1 *ᵥ cb.2 + p.2.2)

/-- Materialize finite coefficient functions once at each syntax node. -/
def cache {α : Type} {n : ℕ} (f : Fin n → α) : Fin n → α :=
  let a := Array.ofFn f
  fun i => a[i.val]'(by simp [a])

@[simp] theorem cache_eq {α : Type} {n : ℕ} (f : Fin n → α) : cache f = f := by
  funext i
  simp [cache]

def coefficientsCached (p : P R d) : FreeMagma (Fin k) → C R d k
  | .Leaf j => (fun i => if i = j then 1 else 0, 0)
  | .Fork a b =>
    let ca := coefficientsCached p a
    let cb := coefficientsCached p b
    let mats := Vector.ofFn (fun i : Fin k => Vector.ofFn (fun j : Fin d =>
      Vector.ofFn (fun l : Fin d => (p.1 * ca.1 i + p.2.1 * cb.1 i) j l)))
    let vec := Vector.ofFn (p.1 *ᵥ ca.2 + p.2.1 *ᵥ cb.2 + p.2.2)
    (fun i j l => ((mats.get i).get j).get l, fun i => vec.get i)


@[csimp] theorem coefficients_eq_cached : @coefficients = @coefficientsCached := by
  funext R inst d k p t
  induction t with
  | Leaf j => rfl
  | Fork a b ha hb =>
    simp only [coefficients, coefficientsCached, ha, hb]
    apply Prod.ext
    · funext i j l; simp [Vector.get]
    · funext i; simp [Vector.get]


def realize (c : C R d k) (φ : Fin k → V R d) : V R d :=
  (∑ j, c.1 j *ᵥ φ j) + c.2

theorem eval_eq_realize (p : P R d) (φ : Fin k → V R d) (t : FreeMagma (Fin k)) :
    @evalInMagma _ _ ⟨op p⟩ φ t = realize (coefficients p t) φ := by
  induction t with
  | Leaf j =>
    simp only [evalInMagma, coefficients, realize, add_zero]
    symm
    calc
      _ = ∑ i : Fin k, if i = j then φ j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = j
        · subst i; simp
        · simp [h]
      _ = φ j := by simp
  | Fork a b ha hb =>
    change op p (@evalInMagma _ _ ⟨op p⟩ φ a) (@evalInMagma _ _ ⟨op p⟩ φ b) = _
    rw [ha, hb]
    simp only [coefficients, realize, op, mulVec_add, mulVec_sum, add_mulVec,
      mulVec_mulVec, Finset.sum_add_distrib]
    abel

theorem realize_injective : Function.Injective (realize (R := R) (d := d) (k := k)) := by
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  have hc : c = e := by simpa [realize] using congrFun h 0
  have ha : a = b := by
    funext j
    apply Matrix.ext_of_mulVec_single
    intro i
    have hi := congrFun h (Pi.single j (Pi.single i 1))
    simpa [realize, Pi.single_apply, hc, apply_ite] using hi
  exact Prod.ext ha hc

def Test (L : MagmaLaw (Fin k)) (p : P R d) : Prop :=
  coefficients p L.lhs = coefficients p L.rhs

instance [DecidableEq R] (L : MagmaLaw (Fin k)) (p : P R d) : Decidable (Test L p) := by
  unfold Test
  infer_instance

theorem test_iff_satisfies (L : MagmaLaw (Fin k)) (p : P R d) :
    Test L p ↔ @satisfies _ (V R d) ⟨op p⟩ L := by
  constructor
  · intro h φ
    unfold satisfiesPhi
    rw [eval_eq_realize, eval_eq_realize, h]
  · intro h
    apply realize_injective
    funext φ
    simpa only [← eval_eq_realize] using h φ

end Magma.MatrixFamily

namespace Magma.MatrixFamily
variable {R : Type} [CommRing R] {d : ℕ}
abbrev LP (R : Type) (d : ℕ) := M R d × M R d
def lin (p : LP R d) := op (p.1, p.2, (0 : V R d))
def linComp (p q r : LP R d) : LP R d :=
  (p.1 * q.1 + p.2 * r.1, p.1 * q.2 + p.2 * r.2)
theorem lin_injective : Function.Injective (lin (R := R) (d := d)) := by
  intro p q h
  have he : ((p.1, p.2, 0) : P R d) = (q.1, q.2, 0) := op_injective h
  apply Prod.ext
  · exact congrArg (fun t : P R d => t.1) he
  · exact congrArg (fun t : P R d => t.2.1) he
theorem lin_fst (x y : V R d) : lin (1, 0) x y = x := op_fst x y
theorem lin_snd (x y : V R d) : lin (0, 1) x y = y := op_snd x y
theorem lin_comp (p q r : LP R d) (x y : V R d) :
    lin (linComp p q r) x y = lin p (lin q x y) (lin r x y) := by
  simpa [lin, linComp, comp] using op_comp (p.1, p.2, (0 : V R d))
    (q.1, q.2, (0 : V R d)) (r.1, r.2, (0 : V R d)) x y
end Magma.MatrixFamily

/-- info: 'Magma.MatrixFamily.test_iff_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.MatrixFamily.test_iff_satisfies
/-- info: 'Magma.MatrixFamily.op_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.MatrixFamily.op_comp
