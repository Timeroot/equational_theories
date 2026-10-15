import equational_theories.Spectrum.Equation63.OrderTen.Normalization

/-! A strengthened normalization for the fourteen-element exclusion.
A Latin table has as many fixed points across its rows as elements. If every
row has a fixed point, each row therefore has exactly one. Otherwise we may
label a row having no fixed points as zero. This avoids counting or sorting
cycle partitions in the finite certificate. -/
namespace Spectrum.E63.OrderFourteen
open OrderTen

variable {A : Type*} [Finite A] {f : A → A → A}

/-- In a Latin table, if every row has a fixed point, it has exactly one.
The proof uses the bijection assigning to each column its fixed-point row. -/
theorem unique_fixed_of_all (h : Cubic f) (hf : ∀ x, ∃ y, f x y = y) :
    ∀ x, ∃! y, f x y = y := by
  let owner (y : A) := f y (f y y)
  have ho (y : A) : f (owner y) y = y := h y y
  have he (x y : A) (hh : f x y = y) : owner y = x :=
    right_injective h y ((ho y).trans hh.symm)
  have hs : Function.Surjective owner := by
    intro x
    obtain ⟨y, hy⟩ := hf x
    exact ⟨y, he x y hy⟩
  have hi := Finite.injective_iff_surjective.mpr hs
  intro x
  obtain ⟨y, hy⟩ := hf x
  exact ⟨y, hy, fun z hz => hi ((he x z hz).trans (he x y hy).symm)⟩

def FixedRule {n : ℕ} [NeZero n] (f : Fin n → Fin n → Fin n) : Prop :=
  (∀ y, f 0 y ≠ y) ∨ (∀ x, ∃! y, f x y = y)

lemma unique_relabel {n : ℕ} (f : Fin n → Fin n → Fin n)
    (hf : ∀ x, ∃! y, f x y = y) (e : Equiv.Perm (Fin n)) :
    ∀ x, ∃! y, e (f (e.symm x) (e.symm y)) = y := by
  intro x
  obtain ⟨y,hy,hu⟩ := hf (e.symm x)
  refine ⟨e y, by simpa using congrArg e hy, ?_⟩
  intro z hz
  have hh : f (e.symm x) (e.symm z) = e.symm z := by
    apply e.injective
    simpa using hz
  have := hu _ hh
  simpa using congrArg e this

/-- Choose zero with no fixed points whenever possible; otherwise choose it
non-idempotent if possible. Then label the cycles of its row consecutively. -/
theorem normalized_cubic {n : ℕ} [NeZero n]
    (f : Fin n → Fin n → Fin n) (h : Cubic f) :
    ∃ g : Fin n → Fin n → Fin n, Cubic g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) ∧
      (∀ y, (g 0 y).val ≤ y.val + 1) ∧ FixedRule g := by
  classical
  have choose_zero : ∃ g : Fin n → Fin n → Fin n, Cubic g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) ∧ FixedRule g := by
    by_cases hz : ∃ x, ∀ y, f x y ≠ y
    · obtain ⟨x,hx⟩ := hz
      let e := Equiv.swap x (0 : Fin n)
      let g (a b : Fin n) := e (f (e.symm a) (e.symm b))
      have he : e.symm 0 = x := Equiv.swap_apply_right x 0
      have hg (y : Fin n) : g 0 y ≠ y := by
        intro hh
        have hh' : f x (e.symm y) = e.symm y := by
          apply e.injective
          simpa only [g, he, Equiv.apply_symm_apply] using hh
        exact hx _ hh'
      exact ⟨g, cubic_relabel h e, fun hh => (hg 0 hh).elim, Or.inl hg⟩
    · have hf : ∀ x, ∃ y, f x y = y := by simpa only [not_exists, not_forall, not_not] using hz
      have hu := unique_fixed_of_all h hf
      by_cases hi : ∀ x, f x x = x
      · exact ⟨f, h, fun _ => hi, Or.inr hu⟩
      · push Not at hi
        obtain ⟨x,hx⟩ := hi
        let e := Equiv.swap x (0 : Fin n)
        let g (a b : Fin n) := e (f (e.symm a) (e.symm b))
        have he : e.symm 0 = x := Equiv.swap_apply_right x 0
        refine ⟨g, cubic_relabel h e, ?_, Or.inr (unique_relabel f hu e)⟩
        intro hg
        have hh : f x x = x := by
          apply e.injective
          simpa only [g, he, e, Equiv.swap_apply_left] using hg
        exact (hx hh).elim
  obtain ⟨g,hg,hd,hf⟩ := choose_zero
  obtain ⟨e,he,hc⟩ := exists_chain_label (g 0)
  have he' : e.symm 0 = 0 := by
    apply e.injective
    simpa using he.symm
  let q (a b : Fin n) := e (g (e.symm a) (e.symm b))
  refine ⟨q, cubic_relabel hg e, ?_, ?_, ?_⟩
  · intro hq x
    have h0 : g 0 0 = 0 := by
      apply e.injective
      simpa only [q, he', he] using hq
    simp only [q, hd h0, Equiv.apply_symm_apply]
  · intro y
    simpa only [q, he'] using hc y
  · rcases hf with hf | hf
    · left
      intro y hy
      apply hf (e.symm y)
      apply e.injective
      simpa only [q, he', Equiv.apply_symm_apply] using hy
    · exact Or.inr (unique_relabel g hf e)

end Spectrum.E63.OrderFourteen
