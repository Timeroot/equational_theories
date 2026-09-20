import equational_theories.Definability.ProjectionFamilyCounting

/-! Left-translation families with a projection and prescribed maps on the kernel. -/
open Law Law.MagmaLaw

namespace Magma.LeftProjectionKernelFamily
variable {A B K I : Type} [AddGroup A] [AddGroup B]
variable (maps : I → B →+ B) (values : K → B → B)

/-- Cover equivariant functions by their values at orbit representatives. -/
theorem function_coverage_of_chart {m h : ℕ}
    (rep : Fin m → B) (tr : B → Fin m × I) (sizes : Fin m → ℕ)
    (choices : (i : Fin m) → Fin (sizes i) → B)
    (stabilizers : Fin m → Fin h → I)
    (htr : ∀ b, maps (tr b).2 (rep (tr b).1) = b)
    (hfix : ∀ i j, maps (stabilizers i j) (rep i) = rep i)
    (hchoices : ∀ i b, (∀ j, maps (stabilizers i j) b = b) → ∃ q, choices i q = b)
    (hcovered : ∀ p : (i : Fin m) → Fin (sizes i), ∃ k, ∀ b,
      values k b = maps (tr b).2 (choices (tr b).1 (p (tr b).1)))
    (f : B → B) (hf : ∀ i b, maps i (f b) = f (maps i b)) :
    ∃ k, values k = f := by
  classical
  have hp : ∀ i, ∃ q, choices i q = f (rep i) := by
    intro i
    apply hchoices i (f (rep i))
    intro j
    rw [hf, hfix]
  choose p hp using hp
  obtain ⟨k, hk⟩ := hcovered p
  refine ⟨k, ?_⟩
  funext b
  rw [hk, hp, hf, htr]

/-- Check orbit representatives and their allowed values, rather than enumerating
every function on the kernel. -/
theorem kernel_coverage_of_chart {m h : ℕ}
    (rep : Fin m → B) (tr : B → Fin m × I) (sizes : Fin m → ℕ)
    (choices : (i : Fin m) → Fin (sizes i) → B)
    (stabilizers : Fin m → Fin h → I)
    (htr : ∀ b, maps (tr b).2 (rep (tr b).1) = b)
    (hfix : ∀ i j, maps (stabilizers i j) (rep i) = rep i)
    (hchoices : ∀ i b, (rep i = 0 → b = 0) →
      (∀ j, maps (stabilizers i j) b = b) → ∃ q, choices i q = b)
    (hcovered : ∀ p : (i : Fin m) → Fin (sizes i), ∃ k, ∀ b,
      values k b = maps (tr b).2 (choices (tr b).1 (p (tr b).1)))
    (f : B → B) (hf0 : f 0 = 0) (hf : ∀ i b, maps i (f b) = f (maps i b)) :
    ∃ k, values k = f := by
  classical
  have hp : ∀ i, ∃ q, choices i q = f (rep i) := by
    intro i
    apply hchoices i (f (rep i))
    · intro hi
      simpa only [hi] using hf0
    · intro j
      rw [hf, hfix]
  choose p hp using hp
  obtain ⟨k, hk⟩ := hcovered p
  refine ⟨k, ?_⟩
  funext b
  rw [hk, hp, hf, htr]

abbrev Params (A K : Type) := (A → A) × (A → K)
def function (p : Params A K) (x : A × B) : A × B :=
  (p.1 x.1, values (p.2 x.1) x.2)
@[implicit_reducible] def fam (p : Params A K) : Magma (A × B) :=
  ⟨fun x y => x + function values p (-x + y)⟩
def lift (f : B →+ B) (x : A × B) : A × B := (x.1, f x.2)
def gen : (A × B) ⊕ Option I → (A × B) → A × B
  | .inl a => fun x => a + x
  | .inr none => fun x => (x.1, 0)
  | .inr (some i) => lift (maps i)

theorem coverage
    (hvalues : ∀ f : B → B, f 0 = 0 → (∀ i x, maps i (f x) = f (maps i x)) →
      ∃ k, values k = f)
    (N : Magma (A × B)) (hg : ∀ i, N.IsEndo (gen maps i)) :
    ∃ p, fam values p = N := by
  classical
  let f : A × B → A × B := fun x => N.op 0 x
  have hp (a : A) (b : B) : (f (a, b)).1 = (f (a, 0)).1 ∧ (f (a, 0)).2 = 0 := by
    have h := hg (.inr none) 0 (a, b)
    change ((f (a, b)).1, (0 : B)) = f (a, 0) at h
    have h₁ := congrArg (fun z : A × B => z.1) h
    have h₂ := congrArg (fun z : A × B => z.2) h
    exact ⟨h₁, h₂.symm⟩
  have hc (a : A) : ∃ k, values k = fun b => (f (a, b)).2 := by
    apply hvalues
    · exact (hp a 0).2
    · intro i b
      have h := hg (.inr (some i)) 0 (a, b)
      change lift (maps i) (f (a, b)) = N.op (lift (maps i) 0) (lift (maps i) (a, b)) at h
      have hz : lift (maps i) (0 : A × B) = 0 := by simp [lift]
      rw [hz] at h
      exact congrArg Prod.snd h
  choose ks hks using hc
  refine ⟨(fun a => (f (a, 0)).1, ks), ?_⟩
  apply congrArg Magma.mk
  funext x y
  have hf (z : A × B) : function values (fun a => (f (a, 0)).1, ks) z = f z := by
    apply Prod.ext
    · exact (hp z.1 z.2).1.symm
    · exact congrFun (hks z.1) z.2
  change x + function values _ (-x + y) = N.op x y
  rw [hf]
  have h := hg (.inl x) 0 (-x + y)
  change x + N.op 0 (-x + y) = N.op (x + 0) (x + (-x + y)) at h
  simpa only [add_zero, add_neg_cancel_left] using h

theorem family_injective (hv : Function.Injective values) :
    Function.Injective (fun p : Params A K => (fam values p).op) := by
  intro p q hpq
  have hf (z : A × B) : function values p z = function values q z := by
    have h := congrFun (congrFun hpq 0) z
    change 0 + function values p (-0 + z) = 0 + function values q (-0 + z) at h
    simpa only [neg_zero, zero_add] using h
  apply Prod.ext
  · funext a
    exact congrArg Prod.fst (hf (a, 0))
  · funext a
    apply hv
    funext b
    exact congrArg Prod.snd (hf (a, b))

theorem family_generators
    (hz : ∀ k, values k 0 = 0)
    (hc : ∀ k i x, maps i (values k x) = values k (maps i x))
    (p : Params A K) : ∀ i, (fam values p).IsEndo (gen maps i) := by
  intro i x y
  cases i with
  | inl a =>
    change a + (x + function values p (-x + y)) =
      (a + x) + function values p (-(a + x) + (a + y))
    simp only [neg_add_rev, add_assoc, neg_add_cancel_left]
  | inr i =>
    cases i with
    | none =>
      change ((x + function values p (-x + y)).1, (0 : B)) =
        (x.1, 0) + function values p (-(x.1, 0) + (y.1, 0))
      apply Prod.ext <;> simp [function, hz]
    | some i =>
      change lift (maps i) (x + function values p (-x + y)) =
        lift (maps i) x + function values p (-lift (maps i) x + lift (maps i) y)
      apply Prod.ext <;> simp [function, lift, hc]

end Magma.LeftProjectionKernelFamily

/-- info: 'Magma.LeftProjectionKernelFamily.kernel_coverage_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.LeftProjectionKernelFamily.kernel_coverage_of_chart
/-- info: 'Magma.LeftProjectionKernelFamily.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.LeftProjectionKernelFamily.coverage
/-- info: 'Magma.LeftProjectionKernelFamily.family_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.LeftProjectionKernelFamily.family_injective
/-- info: 'Magma.LeftProjectionKernelFamily.family_generators' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.LeftProjectionKernelFamily.family_generators
/-- info: 'Magma.LeftProjectionKernelFamily.function_coverage_of_chart' depends on axioms: [Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.LeftProjectionKernelFamily.function_coverage_of_chart
