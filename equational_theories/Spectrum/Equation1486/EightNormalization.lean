import equational_theories.Spectrum.Equation1486.SquareRows

/-! Normalize the smallest square-row image of an eight-element model. -/
namespace Spectrum.E1486.SquareRows

private theorem exists_perm_sets_fix {A : Type*} [Fintype A] [DecidableEq A]
    (S T : Finset A) (hc : S.card = T.card) (a : A) (ha : a ∈ S ↔ a ∈ T) :
    ∃ p : Equiv.Perm A, p a = a ∧ ∀ x, p x ∈ T ↔ x ∈ S := by
  classical
  let e : S ≃ T := Classical.choice (Fintype.card_eq.mp (by simpa using hc))
  let p := e.extendSubtype
  have hp (x : A) : p x ∈ T ↔ x ∈ S := by
    constructor
    · intro hx
      by_contra hn
      exact e.extendSubtype_not_mem x hn hx
    · exact e.extendSubtype_mem x
  let q := Equiv.swap (p a) a
  refine ⟨p.trans q, by simp [q], ?_⟩
  intro x
  change q (p x) ∈ T ↔ x ∈ S
  have hmem : p a ∈ T ↔ a ∈ T := (hp a).trans ha
  have hswap (y : A) : q y ∈ T ↔ y ∈ T := by
    by_cases hy : y = p a
    · subst y
      simpa [q] using hmem.symm
    by_cases hy' : y = a
    · subst y
      simpa [q] using hmem
    simp [q, Equiv.swap_apply_of_ne_of_ne hy hy']
  exact (hswap (p x)).trans (hp x)

private def relabel {A : Type*} (f : A → A → A) (p : Equiv.Perm A) :=
  fun x y => p (f (p.symm x) (p.symm y))

private theorem relabel_law {A : Type*} (f : A → A → A) (p : Equiv.Perm A)
    (h : Lawful f) : Lawful (relabel f p) := by
  intro x y z
  simp only [relabel, Equiv.symm_apply_apply]
  rw [h, Equiv.apply_symm_apply]

private theorem row_relabel {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → A → A) (p : Equiv.Perm A) (x : A) :
    row (relabel f p) x = (row f (p.symm x)).image p := by
  ext z
  simp only [mem_row, Finset.mem_image, relabel, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, ⟨p.symm y, rfl⟩, hy⟩
  · rintro ⟨w, ⟨y, hy⟩, hz⟩
    refine ⟨p y, ?_⟩
    simpa [hy] using hz

private def target (k : ℕ) (inside : Bool) : Finset (Fin 8) :=
  Finset.univ.filter fun x => if inside then x.val < k else 0 < x.val ∧ x.val ≤ k

/-- Every eight-element E1486 model can be relabeled so its square-row at zero
is contained in either {0,1} or {1,2}. -/
theorem normalize_eight (f : Fin 8 → Fin 8 → Fin 8) (h : Lawful f) :
    ∃ g : Fin 8 → Fin 8 → Fin 8, ∃ inside : Bool, Lawful f ∧ Lawful g ∧
      ∀ z, g 0 (g z z) = (if inside then 0 else 1) ∨
        g 0 (g z z) = (if inside then 1 else 2) := by
  classical
  obtain ⟨a, hpos, hsq⟩ := exists_small_row f h
  have hle : (row f a).card ≤ 2 := by
    simp only [Fintype.card_fin] at hsq
    nlinarith
  let p := Equiv.swap a 0
  let f' := relabel f p
  have hp0 : p.symm 0 = a := by simp [p]
  have hrank : (row f' 0).card = (row f a).card := by
    simp only [f', row_relabel, hp0, Finset.card_image_of_injective _ p.injective]
  let k := (row f' 0).card
  have hk : 1 ≤ k ∧ k ≤ 2 := by dsimp [k]; omega
  let inside := decide ((0 : Fin 8) ∈ row f' 0)
  have htc : (target k inside).card = k := by
    rcases hk with ⟨hlo,hhi⟩
    interval_cases k <;> cases inside <;> decide
  have htz : (0 : Fin 8) ∈ row f' 0 ↔ (0 : Fin 8) ∈ target k inside := by
    simp only [target, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hzero : (0 : Fin 8) ∈ row f' 0
    · simp [inside, hzero, show 0 < k by omega]
    · simp [inside, hzero]
  obtain ⟨q, hq0, hq⟩ := exists_perm_sets_fix (row f' 0) (target k inside) htc.symm 0 htz
  have hqi : q.symm 0 = 0 := by
    apply q.injective
    simpa using hq0.symm
  let g := relabel f' q
  have hrow : row g 0 = target k inside := by
    rw [show g = relabel f' q from rfl, row_relabel, hqi]
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (hq y).mpr hy
    · intro hx
      exact Finset.mem_image.mpr ⟨q.symm x, (hq _).mp (by simpa using hx), q.apply_symm_apply x⟩
  refine ⟨g, inside, h, relabel_law f' q (relabel_law f p h), ?_⟩
  intro z
  have hm : g 0 (g z z) ∈ target k inside := by
    rw [← hrow]
    exact (mem_row g 0 _).mpr ⟨z,rfl⟩
  generalize g 0 (g z z) = u at hm ⊢
  cases hi : inside
  · simp [target, hi] at hm ⊢
    have huv : u.val = 1 ∨ u.val = 2 := by omega
    rcases huv with h1 | h2
    · exact Or.inl (Fin.ext h1)
    · exact Or.inr (Fin.ext h2)
  · simp [target, hi] at hm ⊢
    have huv : u.val = 0 ∨ u.val = 1 := by omega
    rcases huv with h0 | h1
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h1)

end Spectrum.E1486.SquareRows
