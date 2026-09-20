import equational_theories.Definability.TransitiveInvariantCounting
import Mathlib.Algebra.Group.Prod

/-! Complete translation families commuting with a projection onto a direct factor. -/

open Law Law.MagmaLaw
namespace Magma.ProjectionFamily
variable {A B : Type}
section Functions
variable [Zero B] [DecidableEq B]

abbrev Params (A B : Type) [Zero B] := (A → A) × ({x : A × B // x.2 ≠ 0} → B)
def projection (x : A × B) : A × B := (x.1, 0)
def function (p : Params A B) (x : A × B) : A × B :=
  (p.1 x.1, if h : x.2 = 0 then 0 else p.2 ⟨x, h⟩)
def encode (f : A × B → A × B) : Params A B :=
  (fun a => (f (a, 0)).1, fun x => (f x.1).2)

theorem function_projection (p : Params A B) (x : A × B) :
    projection (function p x) = function p (projection x) := by
  simp [projection, function]

theorem function_coverage (f : A × B → A × B)
    (hf : ∀ x, projection (f x) = f (projection x)) : function (encode f) = f := by
  funext x
  apply Prod.ext
  · exact (congrArg Prod.fst (hf x)).symm
  · by_cases hx : x.2 = 0
    · have he : projection x = x := by
        apply Prod.ext
        · rfl
        · exact hx.symm
      have h := congrArg Prod.snd (hf x)
      rw [he] at h
      simpa [function, encode, hx, projection] using h
    · simp [function, encode, hx]

theorem function_injective : Function.Injective (fun p : Params A B => function p) := by
  intro p q hpq
  apply Prod.ext
  · funext a
    exact congrArg Prod.fst (congrFun hpq (a, 0))
  · funext x
    have h := congrArg Prod.snd (congrFun hpq x.1)
    simpa only [function, dif_neg x.2] using h

end Functions

variable [AddCommGroup A] [AddCommGroup B] [DecidableEq B]

@[implicit_reducible] def fam (p : Params A B) : Magma (A × B) :=
  ⟨fun x y => x + function p (y - x)⟩
def gen : (A × B) ⊕ Unit → (A × B) → A × B
  | .inl a => fun x => a + x
  | .inr _ => projection

theorem coverage (N : Magma (A × B)) (hg : ∀ i, N.IsEndo (gen i)) : ∃ p, fam p = N := by
  let f : A × B → A × B := fun x => N.op 0 x
  have hf : ∀ x, projection (f x) = f (projection x) := by
    intro x
    have h := hg (.inr ()) 0 x
    change projection (N.op 0 x) = N.op (projection 0) (projection x) at h
    exact h
  refine ⟨encode f, ?_⟩
  apply congrArg Magma.mk
  funext x y
  change x + function (encode f) (y - x) = N.op x y
  rw [function_coverage f hf]
  have h := hg (.inl x) 0 (y - x)
  change x + N.op 0 (y - x) = N.op (x + 0) (x + (y - x)) at h
  simpa only [add_zero, add_sub_cancel] using h

theorem family_injective : Function.Injective (fun p : Params A B => (fam p).op) := by
  intro p q hpq
  apply function_injective
  funext x
  have h := congrFun (congrFun hpq 0) x
  change 0 + function p (x - 0) = 0 + function q (x - 0) at h
  simpa only [sub_zero, zero_add] using h

theorem family_generators (p : Params A B) : ∀ i, (fam p).IsEndo (gen i) := by
  intro i x y
  cases i with
  | inl a =>
    change a + (x + function p (y - x)) = (a + x) + function p ((a + y) - (a + x))
    simp only [add_sub_add_left_eq_sub, add_assoc]
  | inr u =>
    change projection (x + function p (y - x)) =
      projection x + function p (projection y - projection x)
    apply Prod.ext <;> simp [projection, function]

/-- info: 'Magma.ProjectionFamily.function_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms function_coverage
/-- info: 'Magma.ProjectionFamily.function_injective' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms function_injective
/-- info: 'Magma.ProjectionFamily.coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coverage
/-- info: 'Magma.ProjectionFamily.family_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms family_injective
/-- info: 'Magma.ProjectionFamily.family_generators' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms family_generators
end Magma.ProjectionFamily
