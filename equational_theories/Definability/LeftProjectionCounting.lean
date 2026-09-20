import equational_theories.Definability.ProjectionFamilyCounting

/-! Complete projection-compatible families for arbitrary groups, using left translations. -/
namespace Magma.LeftProjectionFamily
variable {A B : Type} [AddGroup A] [AddGroup B] [DecidableEq B]
open ProjectionFamily

@[implicit_reducible] def fam (p : Params A B) : Magma (A × B) :=
  ⟨fun x y => x + function p (-x + y)⟩
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
  change x + function (encode f) (-x + y) = N.op x y
  rw [function_coverage f hf]
  have h := hg (.inl x) 0 (-x + y)
  change x + N.op 0 (-x + y) = N.op (x + 0) (x + (-x + y)) at h
  simpa only [add_zero, add_neg_cancel_left] using h

theorem family_injective : Function.Injective (fun p : Params A B => (fam p).op) := by
  intro p q hpq
  apply function_injective
  funext x
  have h := congrFun (congrFun hpq 0) x
  change 0 + function p (-0 + x) = 0 + function q (-0 + x) at h
  simpa only [neg_zero, zero_add] using h

theorem family_generators (p : Params A B) : ∀ i, (fam p).IsEndo (gen i) := by
  intro i x y
  cases i with
  | inl a =>
    change a + (x + function p (-x + y)) =
      (a + x) + function p (-(a + x) + (a + y))
    simp only [neg_add_rev, add_assoc, neg_add_cancel_left]
  | inr u =>
    change projection (x + function p (-x + y)) =
      projection x + function p (-projection x + projection y)
    apply Prod.ext <;> simp [projection, function]

end Magma.LeftProjectionFamily

/-- info: 'Magma.LeftProjectionFamily.coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.LeftProjectionFamily.coverage
/-- info: 'Magma.LeftProjectionFamily.family_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.LeftProjectionFamily.family_injective
/-- info: 'Magma.LeftProjectionFamily.family_generators' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.LeftProjectionFamily.family_generators
