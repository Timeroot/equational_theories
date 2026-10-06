import equational_theories.Spectrum.SmallPairs.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-! Enumerate injective rows satisfying the chain bound, pruning while extending
each prefix. For size eleven there are only 1024 completed rows, rather than 11!
permutations. Completeness is proved for every size. -/
namespace Spectrum.SmallPairs.ChainRows

def rows (n : ℕ) : (k : ℕ) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (rows n k).flatMap fun f =>
      ((List.finRange n).filter fun z =>
        decide (z.val ≤ k + 1 ∧ ∀ i, f i ≠ z)).map (Fin.snoc f)

theorem mem_rows {n k : ℕ} (f : Fin k → Fin n)
    (hi : Function.Injective f) (hc : ∀ i, (f i).val ≤ i.val + 1) :
    f ∈ rows n k := by
  induction k with
  | zero =>
    have : f = Fin.elim0 := funext fun i => Fin.elim0 i
    simp [rows, this]
  | succ k ih =>
    have hg : Function.Injective (Fin.init f) := by
      intro a b hab
      exact Fin.castSucc_injective k (hi hab)
    have hb : ∀ i, (Fin.init f i).val ≤ i.val + 1 := fun i => hc i.castSucc
    apply List.mem_flatMap.mpr
    refine ⟨Fin.init f, ih _ hg hb, ?_⟩
    apply List.mem_map.mpr
    refine ⟨f (Fin.last k), List.mem_filter.mpr ⟨List.mem_finRange _, ?_⟩, ?_⟩
    · apply decide_eq_true
      refine ⟨hc (Fin.last k), ?_⟩
      intro i he
      have := hi he
      exact (Fin.ne_of_lt i.castSucc_lt_last) this
    · exact Fin.snoc_init_self f

end Spectrum.SmallPairs.ChainRows
