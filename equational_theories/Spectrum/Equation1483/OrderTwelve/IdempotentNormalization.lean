import equational_theories.Spectrum.Equation1483.OrderTwelve.HeadNormalization
import equational_theories.Spectrum.Equation1483.Graph

/-! A nonconstant idempotent row has a distinct image point returning to zero.
Name that point one before the subsequent head and tail normalizations. -/
namespace Spectrum.E1483.OrderTwelve.IdempotentNormalization
open Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalize Normalized Ranks Normalization
abbrev A := Fin 12

lemma core_relabel_image_preserving_square (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (p : Equiv.Perm A)
    (hp0 : p 0 = 0) (hpSq : p (f 0 0) = f 0 0)
    (hp : ∀ z, bound k zero < z.val → p z = z) :
    RankCore (relabel f p) k zero := by
  have hpres (z : A) : (p z).val ≤ bound k zero ↔ z.val ≤ bound k zero := by
    constructor
    · intro hz
      by_contra hn
      rw [hp z (by omega)] at hz
      omega
    · intro hz
      by_contra hn
      have hh := hp (p z) (by omega)
      have he : p z = z := p.injective hh
      rw [he] at hn
      omega
  have hperm (z : A) :
      (if zero then (p z).val < k else 0 < (p z).val ∧ (p z).val ≤ k) ↔
      (if zero then z.val < k else 0 < z.val ∧ z.val ≤ k) := by
    have hh := hpres z
    have hk : 0 < k := by
      have hx := (h.imageZero (f 0 0)).mp ⟨0,rfl⟩
      cases zero <;> simp_all [bound] <;> omega
    have hz : p z = 0 ↔ z = 0 := by
      calc
        p z = 0 ↔ p z = p 0 := by rw [hp0]
        _ ↔ z = 0 := p.injective.eq_iff
    have hv : (p z).val = 0 ↔ z.val = 0 := by simpa only [Fin.ext_iff,Fin.val_zero] using hz
    cases zero <;> simp only [bound,Bool.false_eq_true,↓reduceIte] at hh ⊢ <;> omega
  let g := relabel f p
  have hg := relabel_1483 f p h.source
  letI : Magma A := ⟨g⟩
  have he : Equation1483 A := fun x y z => (hg x y z).symm
  refine {
    source := hg
    dual := CentralDual.dual he
    leftRegular := CentralDual.left_regular he
    rightRegular := CentralDual.right_regular he
    cardEq := row_col_rank g hg
    minimum := ?_
    nonfull := fun x => (rank_bounds g hg x).2
    rankZero := ?_
    imageZero := ?_
    first := ?_
    idemRank := idem_rank g hg
    rowRank := row_edge g hg
    colRank := col_edge g hg }
  · intro x
    change k ≤ rank (relabel f p) x
    rw [rank_relabel]
    exact h.minimum _
  · change rank (relabel f p) 0 = k
    rw [rank_relabel,perm_symm_zero p hp0]
    exact h.rankZero
  · intro z
    have him : (∃ y, g 0 y = z) ↔ ∃ y, f 0 y = p.symm z := by
      simp only [g,relabel,perm_symm_zero p hp0]
      constructor
      · rintro ⟨y,hy⟩
        exact ⟨p.symm y, by simpa using congrArg p.symm hy⟩
      · rintro ⟨y,hy⟩
        exact ⟨p y, by simpa using congrArg p hy⟩
    rw [him, h.imageZero]
    simpa using (hperm (p.symm z)).symm
  · change (if zero then g 0 0 = 0 ∨ g 0 0 = 1 else g 0 0 = 1)
    have h00 : g 0 0 = f 0 0 := by
      simp only [g,relabel,perm_symm_zero p hp0,hpSq]
    rw [h00]
    exact h.first

lemma choose_predecessor (f : A → A → A) (k : Nat) (zero : Bool)
    (hk : 2 ≤ k) (h : RankCore f k zero) :
    ∃ g : A → A → A, RankCore g k zero ∧ (g 0 0 = 0 → g 0 1 = 0) := by
  classical
  by_cases h00 : f 0 0 = 0
  · letI : Magma A := ⟨f⟩
    have he : Equation1483 A := fun x y z => (h.source x y z).symm
    have hOne : ∃ x, f 0 x = 1 := (h.imageZero 1).mpr (by cases zero <;> simp <;> omega)
    obtain ⟨x,hx⟩ := hOne
    have hx0 : f 0 x ≠ 0 := by rw [hx]; decide
    obtain ⟨b,hb,hb0,hret⟩ := Graph.idempotent_image_predecessor he 0 h00 ⟨x,hx0⟩
    change (∃ z, f 0 z = b) at hb
    change f 0 b = 0 at hret
    have hbound : 1 ≤ bound k zero := by cases zero <;> simp [bound] <;> omega
    have hbBound : b.val ≤ bound k zero := by
      obtain ⟨z,hz⟩ := hb
      have hh := output_bound f k zero h z
      simpa only [hz] using hh
    let p : Equiv.Perm A := Equiv.swap 1 b
    have hp0 : p 0 = 0 := by simp [p,Equiv.swap_apply_of_ne_of_ne,hb0.symm]
    have hpSq : p (f 0 0) = f 0 0 := by rw [h00,hp0]
    have htail (i : A) (hi : bound k zero < i.val) : p i = i := by
      apply Equiv.swap_apply_of_ne_of_ne <;> intro heq
      · have hv := congrArg Fin.val heq
        norm_num at hv
        omega
      · have hv := congrArg Fin.val heq
        omega
    have hnew := core_relabel_image_preserving_square f k zero h p hp0 hpSq htail
    have hp1' : p.symm 1 = b := by simp [p]
    refine ⟨relabel f p,hnew,fun _ => ?_⟩
    simp only [relabel,perm_symm_zero p hp0,hp1',hret,hp0]
  · exact ⟨f,h,fun hz => (h00 hz).elim⟩

lemma exists_normalized (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∃ k : Nat, ∃ zero : Bool, ∃ g : A → A → A,
      (2 ≤ k ∧ k < 12) ∧ RankCore g k zero ∧ Sorted g k zero ∧
      (∀ y, (g 0 y).val ≤ y.val+1) ∧ (g 0 0 = 0 → g 0 1 = 0) := by
  obtain ⟨k,zero,g,hk,hg⟩ := Normalized.exists_normalized f h
  obtain ⟨g,hg,hI⟩ := choose_predecessor g k zero hk.1 hg.toRankCore
  have hzero : (g 0 0).val ≤ 1 := by
    have hh := hg.first
    cases zero <;> simp_all
    rcases hh with hh|hh <;> simp [hh]
  obtain ⟨p,hp,ht,hc⟩ := HeadNormalization.chain_bounded (g 0) (bound k zero)
    (output_bound g k zero hg) hzero
  have hp0 : p 0 = 0 := hp 0 (by decide)
  have hp1 : p 1 = 1 := hp 1 (by decide)
  have hp1' : p.symm 1 = 1 := by apply p.injective; simpa using hp1.symm
  have hpSq : p (g 0 0) = g 0 0 := hp _ hzero
  let q := relabel g p
  have hq := HeadNormalization.core_relabel_image g k zero hg p hp0 hp1 ht
  have hqI : q 0 0 = 0 → q 0 1 = 0 := by
    intro hz
    have hq00 : q 0 0 = g 0 0 := by simp only [q,relabel,perm_symm_zero p hp0,hpSq]
    have hq01 : q 0 1 = p (g 0 1) := by simp only [q,relabel,perm_symm_zero p hp0,hp1']
    rw [hq01,hI (hq00.symm.trans hz),hp0]
  obtain ⟨g',hg',hs,hrow⟩ := exists_sorted q k zero hq
  refine ⟨k,zero,g',hk,hg',hs,?_,?_⟩
  · intro y
    by_cases hy : y.val ≤ bound k zero
    · rw [hrow y hy]
      simpa only [q,relabel,perm_symm_zero p hp0] using hc y
    · have hb := output_bound g' k zero hg' y
      omega
  · intro hz
    have h1 : (1:A).val ≤ bound k zero := by cases zero <;> simp [bound] <;> omega
    rw [hrow 1 h1]
    exact hqI ((hrow 0 (by simp)).symm.trans hz)

end Spectrum.E1483.OrderTwelve.IdempotentNormalization
