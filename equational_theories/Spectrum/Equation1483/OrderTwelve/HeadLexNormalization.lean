import equational_theories.Spectrum.Equation1483.OrderTwelve.IdempotentNormalization
import Mathlib.Order.PiLex
import Mathlib.Data.Set.Finite.Lemmas

/-! Choose the least first row lexicographically, then sort only labels outside
its image. This removes the residual permutations of the image head, while
preserving the distinguished zero, one, and idempotent-predecessor condition. -/
namespace Spectrum.E1483.OrderTwelve.HeadLexNormalization
open Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalize Normalized Ranks Normalization
abbrev A := Fin 12

def swapRow (f : A → A → A) (a b i : A) : A :=
  Equiv.swap a b (f 0 (Equiv.swap a b i))

def HeadLex (f : A → A → A) (k : Nat) (zero : Bool) : Prop :=
  ∀ a b i : A, 2 ≤ a.val → a < b → b.val ≤ bound k zero →
      i.val ≤ bound k zero →
      (∀ j : A, j < i → f 0 j = swapRow f a b j) →
      f 0 i ≤ swapRow f a b i

lemma swap_fixed_lt (a b i : A) (hab : a < b) (hi : i < a) :
    Equiv.swap a b i = i := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact ne_of_lt hi
  · exact ne_of_lt (hi.trans hab)

lemma first_small (f : A → A → A) (k : Nat) (zero : Bool) (h : RankCore f k zero) :
    (f 0 0).val ≤ 1 := by
  have hh := h.first
  cases zero <;> simp_all
  rcases hh with hh|hh <;> simp [hh]

lemma swap_core (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hI : f 0 0 = 0 → f 0 1 = 0)
    (a b : A) (ha : 2 ≤ a.val) (hab : a < b) (hb : b.val ≤ bound k zero) :
    RankCore (relabel f (Equiv.swap a b)) k zero ∧
      (relabel f (Equiv.swap a b) 0 0 = 0 → relabel f (Equiv.swap a b) 0 1 = 0) := by
  let p := Equiv.swap a b
  have hp0 : p 0 = 0 := swap_fixed_lt a b 0 hab (by change 0 < a.val; omega)
  have hp1 : p 1 = 1 := swap_fixed_lt a b 1 hab (by change 1 < a.val; omega)
  have hp1' : p.symm 1 = 1 := by apply p.injective; simpa using hp1.symm
  have hpSq : p (f 0 0) = f 0 0 := swap_fixed_lt a b (f 0 0) hab (by
    have := first_small f k zero h
    change (f 0 0).val < a.val
    omega)
  have hpTail (i : A) (hi : bound k zero < i.val) : p i = i := by
    apply Equiv.swap_apply_of_ne_of_ne <;> intro he
    · have hv := congrArg Fin.val he
      have habv : a.val < b.val := hab
      omega
    · have hv := congrArg Fin.val he
      omega
  refine ⟨HeadNormalization.core_relabel_image f k zero h p hp0 hp1 hpTail,?_⟩
  intro hz
  have h00 : relabel f p 0 0 = f 0 0 := by
    simp only [relabel,perm_symm_zero p hp0,hpSq]
  have h01 : relabel f p 0 1 = p (f 0 1) := by
    simp only [relabel,perm_symm_zero p hp0,hp1']
  rw [h01,hI (h00.symm.trans hz),hp0]

lemma exists_head_minimal (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hI : f 0 0 = 0 → f 0 1 = 0) :
    ∃ g : A → A → A, RankCore g k zero ∧ (g 0 0 = 0 → g 0 1 = 0) ∧ HeadLex g k zero := by
  classical
  let S : Set (A → A → A) := {g | RankCore g k zero ∧ (g 0 0 = 0 → g 0 1 = 0)}
  obtain ⟨g,hg,hmin⟩ := Set.exists_min_image S (fun q => toLex (q 0)) S.toFinite ⟨f,h,hI⟩
  refine ⟨g,hg.1,hg.2,?_⟩
  intro a b i ha hab hb hi hpref
  let p := Equiv.swap a b
  let q := relabel g p
  have hq : q ∈ S := swap_core g k zero hg.1 hg.2 a b ha hab hb
  have hrow : q 0 = swapRow g a b := by
    funext j
    have hp0 : p 0 = 0 := swap_fixed_lt a b 0 hab (by change 0 < a.val; omega)
    change p (g (p.symm 0) (p.symm j)) = Equiv.swap a b (g 0 (Equiv.swap a b j))
    rw [perm_symm_zero p hp0]
    rfl
  have hl := hmin q hq
  rw [hrow] at hl
  exact Pi.apply_le_of_toLex hl hpref

lemma swap_within {k : Nat} {zero : Bool} (a b i : A) (hab : a < b) (hb : b.val ≤ bound k zero)
    (hi : i.val ≤ bound k zero) : (Equiv.swap a b i).val ≤ bound k zero := by
  by_cases ha : i = a
  · subst i
    simpa using hb
  by_cases hb' : i = b
  · subst i
    have hh : a.val < b.val := hab
    simpa using (show a.val ≤ bound k zero by omega)
  · simpa [Equiv.swap_apply_of_ne_of_ne ha hb'] using hi

lemma head_congr (f g : A → A → A) (k : Nat) (zero : Bool)
    (hlex : HeadLex f k zero)
    (hr : ∀ i : A, i.val ≤ bound k zero → g 0 i = f 0 i) : HeadLex g k zero := by
  intro a b i ha hab hb hi hpref
  have hswap (j : A) (hj : j.val ≤ bound k zero) :
      swapRow g a b j = swapRow f a b j := by
    unfold swapRow
    rw [hr (Equiv.swap a b j) (swap_within a b j hab hb hj)]
  rw [hr i hi,hswap i hi]
  apply hlex a b i ha hab hb hi
  intro j hj
  have hbound : j.val ≤ bound k zero := by have : j.val < i.val := hj; omega
  have hh := hpref j hj
  rwa [hr j hbound,hswap j hbound] at hh

/-- Lex-minimality forces the usual chain bound, by choosing the first failure. -/
lemma chain_of_headLex (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hlex : HeadLex f k zero) :
    ∀ y, (f 0 y).val ≤ y.val+1 := by
  have induction (m : Nat) : ∀ y : A, y.val = m → (f 0 y).val ≤ y.val+1 := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro y hy
      by_cases hy0 : y = 0
      · subst y
        exact first_small f k zero h
      by_contra hn
      have hv := (f 0 y).isLt
      have hm : 0 < m := by
        have hyv : y.val ≠ 0 := by intro hz; apply hy0; exact Fin.ext hz
        omega
      have haLt : m+1 < 12 := by omega
      let a : A := ⟨m+1,haLt⟩
      let b : A := f 0 y
      have hab : a < b := by change m+1 < (f 0 y).val; omega
      have ha : 2 ≤ a.val := by dsimp [a]; omega
      have hb : b.val ≤ bound k zero := output_bound f k zero h y
      have hi : y.val ≤ bound k zero := by dsimp [b] at hb; omega
      have hpref (j : A) (hj : j < y) : f 0 j = swapRow f a b j := by
        have hjv : j.val < m := by change j.val < y.val at hj; omega
        have hprev := ih j.val hjv j rfl
        have hja : j < a := by change j.val < m+1; omega
        have hfa : f 0 j < a := by change (f 0 j).val < m+1; omega
        simp only [swapRow,swap_fixed_lt a b j hab hja,swap_fixed_lt a b (f 0 j) hab hfa]
      have he := hlex a b y ha hab hb hi hpref
      have hya : y < a := by change y.val < m+1; omega
      simp only [swapRow,swap_fixed_lt a b y hab hya] at he
      change b ≤ Equiv.swap a b b at he
      rw [Equiv.swap_apply_right] at he
      have : (f 0 y).val ≤ m+1 := he
      omega
  exact fun y => induction y.val y rfl

lemma exists_normalized (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∃ k : Nat, ∃ zero : Bool, ∃ g : A → A → A,
      (2 ≤ k ∧ k < 12) ∧ RankCore g k zero ∧ Sorted g k zero ∧
      (∀ y, (g 0 y).val ≤ y.val+1) ∧ (g 0 0 = 0 → g 0 1 = 0) ∧ HeadLex g k zero := by
  obtain ⟨k,zero,g,hk,hg⟩ := Normalized.exists_normalized f h
  obtain ⟨g,hg,hI⟩ := IdempotentNormalization.choose_predecessor g k zero hk.1 hg.toRankCore
  obtain ⟨g,hg,hI,hlex⟩ := exists_head_minimal g k zero hg hI
  obtain ⟨g',hg',hs,hrow⟩ := exists_sorted g k zero hg
  have hlex' : HeadLex g' k zero := head_congr g g' k zero hlex hrow
  refine ⟨k,zero,g',hk,hg',hs,chain_of_headLex g' k zero hg' hlex',?_,hlex'⟩
  intro hz
  have h1 : (1:A).val ≤ bound k zero := by cases zero <;> simp [bound] <;> omega
  rw [hrow 1 h1]
  exact hI ((hrow 0 (by simp)).symm.trans hz)
end Spectrum.E1483.OrderTwelve.HeadLexNormalization
