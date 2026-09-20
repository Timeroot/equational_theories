import equational_theories.Definability.LeftProjectionCounting

open Law Law.MagmaLaw
namespace Magma.EndomorphismFamily
variable {A I K : Type} [AddGroup A]
variable (maps : I → A →+ A) (values : K → A → A)

def gen : A ⊕ I → A → A
  | .inl a => fun x => a + x
  | .inr i => maps i
@[implicit_reducible] def fam (k : K) : Magma A := ⟨fun x y => x + values k (-x + y)⟩

theorem coverage
    (hc : ∀ f : A → A, (∀ i x, maps i (f x) = f (maps i x)) → ∃ k, values k = f)
    (N : Magma A) (hg : ∀ i, N.IsEndo (gen maps i)) : ∃ k, fam values k = N := by
  let f : A → A := fun x => N.op 0 x
  have hf : ∀ i x, maps i (f x) = f (maps i x) := by
    intro i x
    have h := hg (.inr i) 0 x
    change maps i (N.op 0 x) = N.op (maps i 0) (maps i x) at h
    simpa only [map_zero] using h
  obtain ⟨k,hk⟩ := hc f hf
  refine ⟨k, congrArg Magma.mk ?_⟩
  funext x y
  change x + values k (-x + y) = N.op x y
  rw [hk]
  have h := hg (.inl x) 0 (-x + y)
  change x + N.op 0 (-x + y) = N.op (x + 0) (x + (-x + y)) at h
  simpa only [add_zero, add_neg_cancel_left] using h

theorem family_injective (hv : Function.Injective values) :
    Function.Injective (fun k => (fam values k).op) := by
  intro p q h
  apply hv
  funext x
  have h := congrFun (congrFun h 0) x
  change 0 + values p (-0 + x) = 0 + values q (-0 + x) at h
  simpa only [neg_zero,zero_add] using h

theorem family_generators (hc : ∀ k i x, maps i (values k x) = values k (maps i x))
    (k : K) : ∀ i, (fam values k).IsEndo (gen maps i) := by
  intro i x y
  cases i with
  | inl a =>
    change a + (x + values k (-x + y)) = (a + x) + values k (-(a + x) + (a + y))
    simp only [neg_add_rev,add_assoc,neg_add_cancel_left]
  | inr i =>
    change maps i (x + values k (-x + y)) = maps i x + values k (-maps i x + maps i y)
    rw [map_add, hc, map_add, map_neg]

/-- A small set of coordinates determines every commuting function. -/
theorem function_coverage_of_coordinates {r : ℕ}
    (rep : Fin r → A) (tr : A → Fin r × I)
    (htr : ∀ x, maps (tr x).2 (rep (tr x).1) = x)
    (cover : (Fin r → A) → K)
    (hcover : ∀ p : Fin r → A,
      (∀ i x, maps i (maps (tr x).2 (p (tr x).1)) =
        maps (tr (maps i x)).2 (p (tr (maps i x)).1)) →
      ∀ x, values (cover p) x = maps (tr x).2 (p (tr x).1))
    (f : A → A) (hf : ∀ i x, maps i (f x) = f (maps i x)) : ∃ k, values k = f := by
  let p : Fin r → A := fun i => f (rep i)
  have he : ∀ x, maps (tr x).2 (p (tr x).1) = f x := by
    intro x
    dsimp only [p]
    rw [hf,htr]
  refine ⟨cover p, ?_⟩
  funext x
  rw [hcover p (by intro i y; rw [he,he]; exact hf i y), he]
end Magma.EndomorphismFamily

/-- info: 'Magma.EndomorphismFamily.coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.EndomorphismFamily.coverage

/-- info: 'Magma.EndomorphismFamily.family_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.EndomorphismFamily.family_injective

/-- info: 'Magma.EndomorphismFamily.family_generators' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.EndomorphismFamily.family_generators

/-- info: 'Magma.EndomorphismFamily.function_coverage_of_coordinates' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.EndomorphismFamily.function_coverage_of_coordinates
