import equational_theories.Definability.ProjectionKernelCounting

/-! Further restrict a projection family by additive maps on its first factor. -/
namespace Magma.ProjectionBaseFamily
variable {A B K I J P Q : Type} [AddCommGroup A] [AddCommGroup B]
variable (maps : I → B →+ B) (values : K → B → B) (baseMaps : J → A →+ A)
variable (gvalues : P → A → A) (hvalues : Q → A → K)

def baseLift (f : A →+ A) (x : A × B) : A × B := (f x.1, x.2)
def gen : ((A × B) ⊕ Option I) ⊕ J → (A × B) → A × B
  | .inl i => ProjectionKernelFamily.gen maps i
  | .inr j => baseLift (baseMaps j)
@[implicit_reducible] def fam (p : P × Q) : Magma (A × B) :=
  ProjectionKernelFamily.fam values (gvalues p.1, hvalues p.2)

theorem coverage (hv : Function.Injective values)
    (hvaluesCoverage : ∀ f : B → B, f 0 = 0 →
      (∀ i x, maps i (f x) = f (maps i x)) → ∃ k, values k = f)
    (hgCoverage : ∀ g : A → A, (∀ j a, baseMaps j (g a) = g (baseMaps j a)) →
      ∃ p, gvalues p = g)
    (hhCoverage : ∀ h : A → K, (∀ j a, h a = h (baseMaps j a)) →
      ∃ q, hvalues q = h)
    (N : Magma (A × B)) (hg : ∀ i, N.IsEndo (gen maps baseMaps i)) :
    ∃ p, fam values gvalues hvalues p = N := by
  obtain ⟨p, rfl⟩ := ProjectionKernelFamily.coverage maps values hvaluesCoverage N
    (fun i => hg (.inl i))
  have he (j : J) (a : A) (b : B) :
      baseLift (baseMaps j) (ProjectionKernelFamily.function values p (a, b)) =
        ProjectionKernelFamily.function values p (baseLift (baseMaps j) (a, b)) := by
    have h := hg (.inr j) 0 (a, b)
    change baseLift (baseMaps j) (0 + ProjectionKernelFamily.function values p ((a, b) - 0)) =
      baseLift (baseMaps j) 0 + ProjectionKernelFamily.function values p
        (baseLift (baseMaps j) (a, b) - baseLift (baseMaps j) 0) at h
    have hz : baseLift (baseMaps j) (0 : A × B) = 0 := by
      apply Prod.ext <;> simp [baseLift]
    simpa only [hz, sub_zero, zero_add] using h
  obtain ⟨u, hu⟩ := hgCoverage p.1 (fun j a => congrArg Prod.fst (he j a 0))
  have hconst (j : J) (a : A) : p.2 a = p.2 (baseMaps j a) := by
    apply hv
    funext b
    exact congrArg Prod.snd (he j a b)
  obtain ⟨v, hv⟩ := hhCoverage p.2 hconst
  refine ⟨(u, v), ?_⟩
  simp only [fam, hu, hv, Prod.mk.eta]

theorem family_injective (hv : Function.Injective values)
    (hg : Function.Injective gvalues) (hh : Function.Injective hvalues) :
    Function.Injective (fun p => (fam values gvalues hvalues p).op) := by
  intro p q hpq
  have he := ProjectionKernelFamily.family_injective values hv hpq
  exact Prod.ext (hg (congrArg Prod.fst he)) (hh (congrArg Prod.snd he))

theorem family_generators (hz : ∀ k, values k 0 = 0)
    (hc : ∀ k i x, maps i (values k x) = values k (maps i x))
    (hg : ∀ p j a, baseMaps j (gvalues p a) = gvalues p (baseMaps j a))
    (hh : ∀ q j a, hvalues q a = hvalues q (baseMaps j a))
    (p : P × Q) : ∀ i, (fam values gvalues hvalues p).IsEndo (gen maps baseMaps i) := by
  intro i
  cases i with
  | inl i => exact ProjectionKernelFamily.family_generators maps values hz hc _ i
  | inr j =>
    intro x y
    change baseLift (baseMaps j) (x + ProjectionKernelFamily.function values _ (y - x)) =
      baseLift (baseMaps j) x + ProjectionKernelFamily.function values _
        (baseLift (baseMaps j) y - baseLift (baseMaps j) x)
    apply Prod.ext
    · simp [baseLift, ProjectionKernelFamily.function, hg]
    · simp only [baseLift, ProjectionKernelFamily.function, Prod.snd_add, Prod.fst_sub,
        Prod.snd_sub]
      rw [hh, map_sub]

end Magma.ProjectionBaseFamily

/-- info: 'Magma.ProjectionBaseFamily.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.ProjectionBaseFamily.coverage
/-- info: 'Magma.ProjectionBaseFamily.family_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.ProjectionBaseFamily.family_injective
/-- info: 'Magma.ProjectionBaseFamily.family_generators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.ProjectionBaseFamily.family_generators
