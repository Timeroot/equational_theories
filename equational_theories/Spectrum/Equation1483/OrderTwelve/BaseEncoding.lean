import equational_theories.Definability.Central1483SAT

/-! Order-twelve rank assumptions and their CNF soundness. The generic atom,
cardinality and law encodings are shared with the order-eleven proof. -/
namespace Spectrum.E1483.OrderTwelve.CNF
open Std.Sat Magma.Central1483.CNF
set_option maxHeartbeats 2000000
/-- The algebraic and image conditions, independent of how the remaining labels are sorted. -/
structure RankCore (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool) : Prop where
  source : ∀ x y z, f (f y x) (f x (f y z)) = x
  dual : ∀ x y z, f (f (f z y) x) (f x y) = x
  leftRegular : ∀ x y, f x (f (f x y) x) = f x y
  rightRegular : ∀ x y, f (f x (f y x)) x = f y x
  cardEq : ∀ x, (colSet f x).card = rowSize f x
  minimum : ∀ x, k ≤ rowSize f x
  nonfull : ∀ x, rowSize f x < 12
  rankZero : rowSize f 0 = k
  imageZero : ∀ z, (∃ y, f 0 y = z) ↔
    if zero then z.val < k else 0 < z.val ∧ z.val ≤ k
  first : if zero then f 0 0 = 0 ∨ f 0 0 = 1 else f 0 0 = 1
  idemRank : ∀ x, f x x = x → 4 ≤ rowSize f x
  rowRank : ∀ x y, 12 ≤ rowSize f x * rowSize f (f x y)
  colRank : ∀ x y, 12 ≤ rowSize f x * rowSize f (f y x)

/-- The original normalization orders the remaining labels by row-zero output. -/
structure RankAssumptions (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    extends RankCore f k zero where
  sorted : ∀ y : Fin 12, k+1 ≤ y.val → y.val < 11 → f 0 y ≤ f 0 (y+1)


lemma model_nonfullImages (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) : CNF.Sat (meaning f) nonfullImages := by
  apply sat_all1; intro x
  apply sat_append
  · apply sat_cardUpper _ _ _ (rowSet f x) (meaning_row f x)
    have := h.nonfull x
    change rowSize f x ≤ 12-1
    omega
  · apply sat_cardUpper _ _ _ (colSet f x) (meaning_col f x)
    rw [h.cardEq]
    have := h.nonfull x
    omega
lemma model_minimumImages (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) : CNF.Sat (meaning f) (minimumImages k) := by
  apply sat_all1; intro x
  apply sat_append
  · exact sat_cardLower _ _ _ (rowSet f x) (meaning_row f x) (h.minimum x)
  · apply sat_cardLower _ _ _ (colSet f x) (meaning_col f x)
    rw [h.cardEq]
    exact h.minimum x
lemma model_normalizedImage (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) : CNF.Sat (meaning f) (normalizedImage k zero) := by
  apply sat_all1; intro z
  apply sat_single
  have he := h.imageZero z
  cases zero <;> simp_all [CNF.Clause.eval, meaning, row]
lemma model_firstCell (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) : CNF.Sat (meaning f) (firstCell zero) := by
  have he := h.first
  cases zero <;> simp_all [firstCell, CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p]
lemma model_sortedRow (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) (sortedRow k) := by
  apply sat_all1; intro y
  split
  · rename_i hy
    apply sat_all1; intro z
    apply sat_all1; intro w
    split
    · rename_i hzw
      apply sat_single
      by_cases hz : f 0 y = z
      · have hn : f 0 (y+1) ≠ w := by
          intro hw
          have hs := h.sorted y hy.1 hy.2
          rw [hz,hw] at hs
          exact (not_le.mpr hzw.2.2) hs
        simp [CNF.Clause.eval, meaning, p, hn]
      · simp [CNF.Clause.eval, meaning, p, hz]
    · exact CNF.sat_empty
  · exact CNF.sat_empty




variable {α β : Type*}

lemma rank_threshold_disjunction (r s t u : Nat) (hn : 12 ≤ r*s)
    (ht : (t,u) ∈ [(3,6),(4,4),(6,3)]) : t ≤ r ∨ u ≤ s := by
  by_contra h
  push Not at h
  have hr : r ≤ t-1 := by omega
  have hs : s ≤ u-1 := by omega
  have hm := Nat.mul_le_mul hr hs
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
  rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num at hm <;> omega

lemma model_guarded_lower (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (t : Nat) (ht : t ∈ [3,4,6]) (x : Fin 12) :
    CNF.Sat (meaning f) (guard (flag t x,false) (cardLower (row x) t) ++
      guard (flag t x,false) (cardLower (col x) t)) := by
  by_cases hx : t ≤ rowSize f x
  · apply sat_append
    · apply sat_guard
      right
      exact sat_cardLower _ _ _ (rowSet f x) (meaning_row f x) hx
    · apply sat_guard
      right
      apply sat_cardLower _ _ _ (colSet f x) (meaning_col f x)
      rw [h.cardEq]
      exact hx
  · apply sat_append <;> apply sat_guard <;> left <;>
      simp [meaning_flag f t ht, hx]

lemma model_thresholdExtras (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) : CNF.Sat (meaning f) thresholdExtras := by
  apply sat_append
  · apply sat_append
    · apply sat_allList
      intro t ht
      apply sat_all1; intro x
      exact model_guarded_lower f k zero h t ht x
    · apply sat_all1; intro x
      apply sat_single
      by_cases hi : f x x = x
      · have hr := h.idemRank x hi
        simp [CNF.Clause.eval, meaning, p, flag, hr]
      · simp [CNF.Clause.eval, meaning, p, flag, hi]
  · apply sat_all1; intro x
    apply sat_all1; intro y
    apply sat_allList; intro edge he
    apply sat_allList; intro ts hts
    have ht : ts.1 ∈ [3,4,6] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hts ⊢
      rcases hts with rfl | rfl | rfl <;> simp
    have hu : ts.2 ∈ [3,4,6] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hts ⊢
      rcases hts with rfl | rfl | rfl <;> simp
    apply sat_single
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · by_cases hy : ∃ z, f x z = y
      · obtain ⟨z,hz⟩ := hy
        have hb : 12 ≤ rowSize f x * rowSize f y := by simpa only [hz] using h.rowRank x z
        have hd := rank_threshold_disjunction _ _ _ _ hb hts
        rcases hd with hd | hd <;>
          simp [CNF.Clause.eval, meaning_flag f _ ht, meaning_flag f _ hu, hd]
      · simp [CNF.Clause.eval, meaning, row, hy]
    · by_cases hy : ∃ z, f z x = y
      · obtain ⟨z,hz⟩ := hy
        have hb : 12 ≤ rowSize f x * rowSize f y := by simpa only [hz] using h.colRank x z
        have hd := rank_threshold_disjunction _ _ _ _ hb hts
        rcases hd with hd | hd <;>
          simp [CNF.Clause.eval, meaning_flag f _ ht, meaning_flag f _ hu, hd]
      · simp [CNF.Clause.eval, meaning, col, hy]

lemma model_rankThreeExtras (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) : CNF.Sat (meaning f) rankThreeExtras := by
  apply sat_append
  · apply sat_all1; intro x
    apply sat_append
    · by_cases hx : 4 ≤ rowSize f x
      · apply sat_append
        · apply sat_guard
          right
          exact sat_cardLower _ _ _ (rowSet f x) (meaning_row f x) hx
        · apply sat_guard
          right
          apply sat_cardLower _ _ _ (colSet f x) (meaning_col f x)
          rw [h.cardEq]
          exact hx
      · apply sat_append <;> apply sat_guard <;> left <;> simp [meaning, large, hx]
    · apply sat_single
      by_cases hi : f x x = x
      · have hr := h.idemRank x hi
        simp [CNF.Clause.eval, meaning, p, large, hr]
      · simp [CNF.Clause.eval, meaning, p, large, hi]
  · apply sat_all1; intro x
    apply sat_all1; intro y
    apply sat_two
    · by_cases hy : ∃ z, f x z = y
      · obtain ⟨z,hz⟩ := hy
        have hb : 12 ≤ rowSize f x * rowSize f y := by simpa only [hz] using h.rowRank x z
        have hd := rank_threshold_disjunction _ _ 4 4 hb (by simp)
        rcases hd with hd | hd <;> simp [CNF.Clause.eval, meaning, large, hd]
      · simp [CNF.Clause.eval, meaning, row, hy]
    · by_cases hy : ∃ z, f z x = y
      · obtain ⟨z,hz⟩ := hy
        have hb : 12 ≤ rowSize f x * rowSize f y := by simpa only [hz] using h.colRank x z
        have hd := rank_threshold_disjunction _ _ 4 4 hb (by simp)
        rcases hd with hd | hd <;> simp [CNF.Clause.eval, meaning, large, hd]
      · simp [CNF.Clause.eval, meaning, col, hy]

lemma model_rankFormula (f : Fin 12 → Fin 12 → Fin 12) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) (rankFormula 12 k zero) := by
  have hc : CNF.Sat (meaning f) (cardUpper (col 0) k) := by
    apply sat_cardUpper _ _ _ (colSet f 0) (meaning_col f 0)
    rw [h.cardEq, h.rankZero]
  have ht : CNF.Sat (meaning f) (if k=3 then rankThreeExtras else .empty) := by
    split
    · exact model_rankThreeExtras f k zero h.toRankCore
    · exact CNF.sat_empty
  simp only [rankFormula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨model_formula f h.source h.dual,
    model_exactImages f⟩, model_regularImages f h.leftRegular h.rightRegular⟩,
    model_nonfullImages f k zero h.toRankCore⟩, model_minimumImages f k zero h.toRankCore⟩,
    model_normalizedImage f k zero h.toRankCore⟩, hc⟩, model_firstCell f k zero h.toRankCore⟩, ht⟩,
    model_sortedRow f k zero h⟩, model_thresholdExtras f k zero h.toRankCore⟩


end Spectrum.E1483.OrderTwelve.CNF
