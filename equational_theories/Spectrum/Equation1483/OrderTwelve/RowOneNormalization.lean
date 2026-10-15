import equational_theories.Spectrum.Equation1483.OrderTwelve.HeadNormalization
import Mathlib.Order.PiLex
import Mathlib.Data.Set.Finite.Lemmas

/-! Break the remaining permutations inside row-zero fibers. Such a permutation
fixes both normalized translation images and the whole first row. Choosing the
least second row makes its first mention of interchangeable labels ordered. -/
namespace Spectrum.E1483.OrderTwelve.RowOneNormalization
open Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalize Normalized Ranks Normalization
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
abbrev A := Fin 12
abbrev Op := A → A → A

def FirstMention (f : Op) (k : Nat) (zero : Bool) : Prop :=
  ∀ a b i : A, bound k zero < a.val → a < b → i < a →
    (¬ ∃ x, f x 0 = a) → (¬ ∃ x, f x 0 = b) → f 0 a = f 0 b →
    f 1 i = b → ∃ j : A, j < i ∧ (f 1 j = a ∨ f 1 j = b)

lemma swap_properties (f : Op) (k : Nat) (zero : Bool) (h : RankCore f k zero)
    (hs : Sorted f k zero) (a b : A) (ha : bound k zero < a.val) (hab : a < b)
    (hca : ¬ ∃ x, f x 0 = a) (hcb : ¬ ∃ x, f x 0 = b) (hv : f 0 a = f 0 b) :
    RankCore (relabel f (Equiv.swap a b)) k zero ∧
    Sorted (relabel f (Equiv.swap a b)) k zero ∧
    (∀ x, relabel f (Equiv.swap a b) 0 x = f 0 x) := by
  let p := Equiv.swap a b
  have hp (x : A) (hx : x.val ≤ bound k zero) : p x = x := by
    apply Equiv.swap_apply_of_ne_of_ne <;> intro he
    · subst x; omega
    · subst x; have := (Fin.lt_def.mp hab); omega
  have hr (x : A) : f 0 (p x) = f 0 x := by
    by_cases hx : x = a
    · subst x; simpa [p] using hv.symm
    by_cases hx' : x = b
    · subst x; simpa [p] using hv
    rw [show p x = x from Equiv.swap_apply_of_ne_of_ne hx hx']
  have hkey : key f a = key f b := by simp [key,hca,hcb,hv]
  have hk (x : A) : key f (p x) = key f x := by
    by_cases hx : x = a
    · subst x; simpa [p] using hkey.symm
    by_cases hx' : x = b
    · subst x; simpa [p] using hkey
    rw [show p x = x from Equiv.swap_apply_of_ne_of_ne hx hx']
  refine ⟨core_relabel f k zero h p hp, ?_, ?_⟩
  · intro i j hi hj hij
    rw [key_relabel f k zero h p hp i, key_relabel f k zero h p hp j]
    change key f (p i) ≤ key f (p j)
    rw [hk i,hk j]
    exact hs i j hi hj hij
  · intro x
    rw [row_relabel f k zero h p hp]
    exact hr x

/-- Refine any image-sorted model while keeping its complete first row. -/
lemma refine_model (f : Op) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hs : Sorted f k zero) (hk : 2 ≤ k) :
    ∃ g : Op, RankCore g k zero ∧ Sorted g k zero ∧
      (∀ x, g 0 x = f 0 x) ∧ FirstMention g k zero := by
  classical
  let S : Set Op := {g |
    RankCore g k zero ∧ Sorted g k zero ∧ ∀ x, g 0 x = f 0 x}
  have hf : f ∈ S := ⟨h,hs,fun _ => rfl⟩
  obtain ⟨g,hg,hmin⟩ := Set.exists_min_image S (fun g => toLex (g 1)) S.toFinite ⟨f,hf⟩
  have hgg : RankCore g k zero ∧ Sorted g k zero ∧ ∀ x, g 0 x = f 0 x :=
    hg
  refine ⟨g,hgg.1,hgg.2.1,hgg.2.2,?_⟩
  intro a b i ha hab hia hca hcb hv hval
  by_contra hn
  have hprev (j : A) (hj : j < i) : g 1 j ≠ a ∧ g 1 j ≠ b := by
    constructor <;> intro he
    · exact hn ⟨j,hj,Or.inl he⟩
    · exact hn ⟨j,hj,Or.inr he⟩
  let p := Equiv.swap a b
  let g' := relabel g p
  obtain ⟨hc,hs',hr⟩ := swap_properties g k zero hgg.1 hgg.2.1 a b ha hab hca hcb hv
  have hg' : g' ∈ S := by
    exact ⟨hc,hs',fun x => (hr x).trans (hgg.2.2 x)⟩
  have hbnd : 1 ≤ bound k zero := by cases zero <;> simp [bound] <;> omega
  have hp1 : p 1 = 1 := by
    apply Equiv.swap_apply_of_ne_of_ne <;> intro he
    · have hh := congrArg Fin.val he; norm_num at hh; omega
    · have hh := congrArg Fin.val he; norm_num at hh
      have := Fin.lt_def.mp hab; omega
  have hps1 : p.symm 1 = 1 := by change p 1 = 1; exact hp1
  have fixed (j : A) (hj : j < a) : p j = j := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact ne_of_lt hj
    · exact ne_of_lt (hj.trans hab)
  have hless : toLex (g' 1) < toLex (g 1) := by
    change Pi.Lex (· < ·) (· < ·) (g' 1) (g 1)
    refine ⟨i,?_,?_⟩
    · intro j hj
      change p (g (p.symm 1) (p.symm j)) = g 1 j
      rw [hps1]
      change p (g 1 (p j)) = g 1 j
      rw [fixed j (hj.trans hia)]
      exact Equiv.swap_apply_of_ne_of_ne (hprev j hj).1 (hprev j hj).2
    · change p (g (p.symm 1) (p.symm i)) < g 1 i
      rw [hps1]
      change p (g 1 (p i)) < g 1 i
      rw [fixed i hia,hval]
      simpa [p] using hab
  exact (not_lt_of_ge (hmin g' hg')) hless

end Spectrum.E1483.OrderTwelve.RowOneNormalization
