import equational_theories.Spectrum.Equation467.OrderTwelve.Encoding
import equational_theories.Spectrum.Equation1110.RowNormalization

/-! Preserve the squaring permutation while naming unused labels in row zero.
The first two entries are 1 and the square-root of 0, both in the fixed support. -/
namespace Spectrum.E467.OrderTwelve
open FixedEncoding
open E1110.RowNormalization (chain_label_prefix_offset)

variable {n : ℕ} [NeZero n]

def relabel (f : Fin n → Fin n → Fin n) (e : Equiv.Perm (Fin n))
    (x y : Fin n) : Fin n := e (f (e.symm x) (e.symm y))

omit [NeZero n] in
theorem holds_relabel (f : Fin n → Fin n → Fin n) (h : Holds f)
    (e : Equiv.Perm (Fin n)) : Holds (relabel f e) := by
  intro x y
  simpa only [relabel,Equiv.symm_apply_apply,Equiv.apply_symm_apply] using
    congrArg e (h (e.symm x) (e.symm y))

theorem normalize_idempotent (f : Fin n → Fin n → Fin n) (h : Holds f)
    (hd : ∀ x, f x x = x) :
    ∃ g : Fin n → Fin n → Fin n, Holds g ∧ (∀ x, g x x = x) ∧
      (∀ y, (g 0 y).val ≤ y.val + 1) := by
  obtain ⟨e,he,hc⟩ := E63.OrderTen.exists_chain_label (f 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  refine ⟨relabel f e, holds_relabel f h e, ?_, ?_⟩
  · intro x; simp only [relabel,hd,Equiv.apply_symm_apply]
  · intro y; simpa only [relabel,he'] using hc y

theorem normalize_supported_row {n : ℕ} [NeZero n] (k : ℕ)
    (hk : 4 ≤ k) (hn : k ≤ n)
    (d : Equiv.Perm (Fin n)) (hzero : d 0 = 1)
    (hfix : ∀ x : Fin n, k ≤ x.val → d x = x)
    (f : Fin n → Fin n → Fin n) (h : Holds f)
    (hD : ∀ x, f x x = d x) :
    ∃ g : Fin n → Fin n → Fin n,
      Holds g ∧ (∀ x, g x x = d x) ∧
      (∀ y, (g 0 y).val ≤ y.val + (k - 2)) := by
  have h00 : f 0 0 = 1 := (hD 0).trans hzero
  have h01 : d (f 0 1) = 0 := by
    simpa only [square, root, hD, hzero] using square_root f h 0
  have h01bound : (f 0 1).val < k := by
    by_contra hh
    have hf := hfix (f 0 1) (by omega)
    rw [hf] at h01
    rw [h01] at hh
    simp at hh
    omega
  have hprefix : ∀ i : Fin n, i.val < 2 → (f 0 i).val ≤ i.val + (k - 2) := by
    intro i hi
    have hh : i = 0 ∨ i = 1 := by
      have hone : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      have hz : (0 : Fin n).val = 0 := rfl
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with hi | hi
      · exact Or.inl (Fin.ext (hi.trans hz.symm))
      · exact Or.inr (Fin.ext (hi.trans hone.symm))
    rcases hh with rfl | rfl
    · have hv : (f 0 0).val = 1 := by rw [h00]; simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      have hz : (0 : Fin n).val = 0 := rfl
      omega
    · have hone : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      omega
  obtain ⟨e, he, hc⟩ := chain_label_prefix_offset (f 0) 2 (k - 2) (by omega) hprefix
  have he0 : e 0 = 0 := he 0 (by simp)
  have he0' : e.symm 0 = 0 := by apply e.injective; simpa using he0.symm
  have commutes (x : Fin n) : e (d x) = d (e x) := by
    by_cases hx : x.val < k
    · have hdx : (d x).val < k := by
        by_contra hh
        have hh' : d (d x) = d x := hfix (d x) (by omega)
        have hh'' : d x = x := d.injective hh'
        rw [hh''] at hh
        exact hh hx
      rw [he x (by omega), he (d x) (by omega)]
    · have hex : k ≤ (e x).val := by
        by_contra hh
        have heex := he (e x) (by omega)
        have hexx : e x = x := e.injective heex
        rw [hexx] at hh
        omega
      rw [hfix x (by omega), hfix (e x) hex]
  let g (x y : Fin n) := e (f (e.symm x) (e.symm y))
  refine ⟨g, holds_relabel f h e, ?_, ?_⟩
  · intro x
    change e (f (e.symm x) (e.symm x)) = d x
    rw [hD, commutes, e.apply_symm_apply]
  · intro y
    simpa only [g, he0'] using hc y


end Spectrum.E467.OrderTwelve
