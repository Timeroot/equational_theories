import equational_theories.Spectrum.PBD.Model

/-! Balanced certificate lookup. Every lookup lands in a certified leaf;
there is no reliance on array bounds or external evaluation. -/
namespace Spectrum.PBD

inductive NatTable where
  | leaf : ℕ → NatTable
  | branch : ℕ → NatTable → NatTable → NatTable

namespace NatTable

def get : NatTable → ℕ → ℕ
  | .leaf n, _ => n
  | .branch w l r, i => if i < w then l.get i else r.get (i-w)

def All (P : ℕ → Prop) : NatTable → Prop
  | .leaf n => P n
  | .branch _ l r => l.All P ∧ r.All P

def values : NatTable → List ℕ
  | .leaf n => [n]
  | .branch _ l r => l.values ++ r.values

theorem all_mem {P : ℕ → Prop} {t : NatTable} (h : t.All P)
    {n : ℕ} (hn : n ∈ t.values) : P n := by
  induction t with
  | leaf m =>
    have he : n = m := by simpa only [values, List.mem_singleton] using hn
    exact he ▸ h
  | branch w l r hl hr =>
    rcases List.mem_append.mp hn with hn | hn
    · exact hl h.1 hn
    · exact hr h.2 hn

theorem all_get {P : ℕ → Prop} {t : NatTable} (h : t.All P) (i : ℕ) : P (t.get i) := by
  induction t generalizing i with
  | leaf n => exact h
  | branch w l r hl hr =>
    simp only [get]
    split
    · exact hl h.1 i
    · exact hr h.2 (i-w)

end NatTable

/-- Extend certified overlapping integer intervals. -/
theorem interval_extend {P : ℕ → Prop} {a b c d : ℕ}
    (h : ∀ n, a ≤ n → n ≤ b → P n)
    (g : ∀ n, c ≤ n → n ≤ d → P n) (hc : c ≤ b+1) :
    ∀ n, a ≤ n → n ≤ d → P n := by
  intro n ha hd
  by_cases hb : n ≤ b
  · exact h n ha hb
  · exact g n (by omega) hd

end Spectrum.PBD
