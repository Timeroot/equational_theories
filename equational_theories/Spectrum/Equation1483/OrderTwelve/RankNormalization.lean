import equational_theories.Spectrum.Equation1483.OrderTwelve.BaseEncoding
import equational_theories.Definability.Central1483Normalization
import equational_theories.Spectrum.Equation1483.ConstantSpectrum

/-! Rank normalization at order twelve. A constant or bijective row would force
power-of-two cardinality, so all translation ranks lie between two and eleven. -/
set_option maxHeartbeats 2000000
namespace Spectrum.E1483.OrderTwelve.Normalize
export Magma.Central1483.Normalize
  (swap_mem_iff exists_perm_sets_fix exists_perm_sets_fix_value relabel relabel_trans
   relabel_1483 rowImage mem_rowImage rowImage_relabel card_rowImage_relabel)
end Spectrum.E1483.OrderTwelve.Normalize
namespace Spectrum.E1483.OrderTwelve.Normalize
def targetSet (k : Nat) (zero : Bool) : Finset (Fin 12) :=
  Finset.univ.filter fun x => if zero then x.val < k else 0 < x.val ∧ x.val ≤ k

lemma targetSet_card (k : Nat) (hk : 2 ≤ k ∧ k < 12) (zero : Bool) :
    (targetSet k zero).card = k := by
  obtain ⟨hk0, hk1⟩ := hk
  interval_cases k <;> cases zero <;> decide

lemma targetSet_zero (k : Nat) (hk : 2 ≤ k ∧ k < 12) (zero : Bool) :
    (0 : Fin 12) ∈ targetSet k zero ↔ zero = true := by
  cases zero <;> simp [targetSet] <;> omega

lemma targetSet_one (k : Nat) (hk : 2 ≤ k ∧ k < 12) (zero : Bool) :
    (1 : Fin 12) ∈ targetSet k zero := by
  cases zero <;> simp [targetSet] <;> omega

lemma exists_normal_image (f : Fin 12 → Fin 12 → Fin 12) (k : Nat)
    (hk : 2 ≤ k ∧ k < 12) (hc : (rowImage f 0).card = k) :
    ∃ zero : Bool, ∃ p : Equiv.Perm (Fin 12), p 0 = 0 ∧
      rowImage (relabel f p) 0 = targetSet k zero ∧
      (relabel f p 0 0 = 0 ∨ relabel f p 0 0 = 1) := by
  classical
  let zero := decide ((0 : Fin 12) ∈ rowImage f 0)
  have he : (0 : Fin 12) ∈ rowImage f 0 ↔ (0 : Fin 12) ∈ targetSet k zero := by
    rw [targetSet_zero k hk]
    simp [zero]
  obtain ⟨p, hp0, hp, hb⟩ := exists_perm_sets_fix_value (rowImage f 0) (targetSet k zero)
    (hc.trans (targetSet_card k hk zero).symm) he (f 0 0)
    ((mem_rowImage f 0 _).mpr ⟨0, rfl⟩) (targetSet_one k hk zero) (by decide)
  have hi : p.symm 0 = 0 := by
    apply p.injective
    simpa using hp0.symm
  refine ⟨zero, p, hp0, ?_, ?_⟩
  · rw [rowImage_relabel, hi]
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hp y).mpr hy
    · intro hx
      exact ⟨p.symm x, (hp _).mp (by simpa using hx), p.apply_symm_apply x⟩
  · simpa [relabel, hi] using hb

end Spectrum.E1483.OrderTwelve.Normalize

namespace Spectrum.E1483.OrderTwelve.Normalize

lemma exists_sort_tail (f : Fin 12 → Fin 12 → Fin 12) (k : Nat)
    (hf : ∀ x, (f 0 x).val ≤ k) :
    ∃ p : Equiv.Perm (Fin 12), (∀ x : Fin 12, x.val ≤ k → p x = x) ∧
      ∀ i j : Fin 12, k < i.val → k < j.val → i ≤ j →
        relabel f p 0 i ≤ relabel f p 0 j := by
  classical
  let H : Finset (Fin 12) := Finset.univ.filter (fun x => k < x.val)
  let e := H.orderIsoOfFin rfl
  let σ := Tuple.sort (fun x => f 0 (e x).val)
  let q := σ.extendDomain e.toEquiv
  have hqfix (x : Fin 12) (hx : x.val ≤ k) : q x = x := by
    apply Equiv.Perm.extendDomain_apply_not_subtype
    simpa [H] using (not_lt.mpr hx)
  have hpfix (x : Fin 12) (hx : x.val ≤ k) : q.symm x = x := by
    apply q.injective
    simpa using (hqfix x hx).symm
  refine ⟨q.symm, hpfix, ?_⟩
  have hrelabel (x : Fin 12) : relabel f q.symm 0 x = f 0 (q x) := by
    simp only [relabel, Equiv.symm_symm]
    rw [hqfix 0 (by simp), hpfix _ (hf _)]
  intro i j hi hj hij
  rw [hrelabel, hrelabel]
  have hiH : i ∈ H := by simpa [H] using hi
  have hjH : j ∈ H := by simpa [H] using hj
  have hiq : q i = e (σ (e.symm ⟨i, hiH⟩)) :=
    Equiv.Perm.extendDomain_apply_subtype σ e.toEquiv hiH
  have hjq : q j = e (σ (e.symm ⟨j, hjH⟩)) :=
    Equiv.Perm.extendDomain_apply_subtype σ e.toEquiv hjH
  rw [hiq, hjq]
  exact Tuple.monotone_sort (fun x => f 0 (e x).val) (e.symm.monotone hij)

end Spectrum.E1483.OrderTwelve.Normalize

set_option maxHeartbeats 1000000
namespace Spectrum.E1483.OrderTwelve.Ranks
abbrev A := Fin 12
def image (f : A → A → A) (a : A) : Finset A :=
  Finset.univ.filter (fun z => ∃ y, f a y = z)
def rank (f : A → A → A) (a : A) : Nat := (image f a).card

lemma no_constant (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ¬ ∃ a b, ∀ z, f a z = b := by
  rintro ⟨a,b,hb⟩
  letI : Magma A := ⟨f⟩
  have he : Equation1483 A := fun x y z => (h x y z).symm
  obtain ⟨k, hk⟩ := Spectrum.E1483.Constant.card_pow_two he a b hb
  have hk' : 12 = 2 ^ k := by simpa [A, Nat.card_eq_fintype_card] using hk
  have hlt : k < 4 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 4 ≤ k by omega)
    norm_num at hp
    omega
  interval_cases k <;> norm_num at hk'

lemma rank_bounds (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) (a : A) :
    2 ≤ rank f a ∧ rank f a < 12 := by
  classical
  have hm (z : A) : f a z ∈ image f a := by simp [image]
  have hpos : 0 < rank f a := Finset.card_pos.mpr ⟨f a 0,hm 0⟩
  have hne : rank f a ≠ 1 := by
    intro hr
    obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hr
    apply no_constant f h
    refine ⟨a,b,?_⟩
    intro z
    have hz := hm z
    rw [hb,Finset.mem_singleton] at hz
    exact hz
  have hle : rank f a ≤ 12 := by
    have := Finset.card_le_card (Finset.subset_univ (image f a))
    simpa [rank,A] using this
  have hne11 : rank f a ≠ 12 := by
    intro hr
    have him : image f a = Finset.univ := Finset.eq_of_subset_of_card_le
      (Finset.subset_univ _) (by simpa [A,rank] using le_of_eq hr.symm)
    have hsurj : Function.Surjective (f a) := by
      intro b
      have hb : b ∈ image f a := by simp [him]
      simpa [image] using hb
    letI : Magma A := ⟨f⟩
    have he : Equation1483 A := fun x y z => (h x y z).symm
    have hb := CentralConstant.bijective_row_gives_constant he a
      ⟨(Finite.injective_iff_surjective).mpr hsurj,hsurj⟩
    exact no_constant f h hb
  omega

lemma rank_natCard (f : A → A → A) (a : A) :
    rank f a = Nat.card {z : A // ∃ y, f a y = z} := by
  classical
  simp [rank,image,Nat.card_eq_fintype_card,Fintype.card_subtype]

lemma row_col_rank (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) (a : A) :
    (Finset.univ.filter (fun z => ∃ y, f y a = z)).card = rank f a := by
  classical
  letI : Magma A := ⟨f⟩
  have he : Equation1483 A := fun x y z => (h x y z).symm
  have hc := Nat.card_congr (CentralDual.translationImageEquiv he a)
  rw [rank_natCard]
  simpa [Nat.card_eq_fintype_card,Fintype.card_subtype] using hc.symm

lemma row_edge (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) (a z : A) :
    12 ≤ rank f a * rank f (f a z) := by
  letI : Magma A := ⟨f⟩
  have he : Equation1483 A := fun x y z => (h x y z).symm
  rw [rank_natCard,rank_natCard]
  simpa [A,Nat.card_eq_fintype_card] using CentralDual.row_edge_rank_bound he a z

lemma col_edge (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) (a z : A) :
    12 ≤ rank f a * rank f (f z a) := by
  letI : Magma A := ⟨f⟩
  have he : Equation1483 A := fun x y z => (h x y z).symm
  rw [rank_natCard,rank_natCard]
  simpa [A,Nat.card_eq_fintype_card] using CentralDual.col_edge_rank_bound he a z

lemma idem_rank (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) (a : A) (ha : f a a = a) :
    4 ≤ rank f a := by
  have hb := row_edge f h a a
  rw [ha] at hb
  nlinarith

end Spectrum.E1483.OrderTwelve.Ranks

namespace Spectrum.E1483.OrderTwelve.Normalized
open Spectrum.E1483.OrderTwelve.Normalize Spectrum.E1483.OrderTwelve.Ranks
abbrev A := Fin 12

lemma rank_image (f : A → A → A) (x : A) :
    rank f x = (rowImage f x).card := by
  apply congrArg Finset.card
  ext z
  simp only [image, Finset.mem_filter, Finset.mem_univ, true_and, mem_rowImage]

lemma rank_relabel (f : A → A → A) (p : Equiv.Perm A) (x : A) :
    rank (relabel f p) x = rank f (p.symm x) := by
  rw [rank_image,card_rowImage_relabel,← rank_image]

lemma perm_symm_zero (p : Equiv.Perm A) (h : p 0 = 0) : p.symm 0 = 0 := by
  apply p.injective
  simpa using h.symm

lemma assumptions_of_normal (f : A → A → A) (k : Nat) (zero : Bool)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (hmin : ∀ x, k ≤ rank f x) (hzero : rank f 0 = k)
    (him : rowImage f 0 = targetSet k zero)
    (hfirst : f 0 0 = 0 ∨ f 0 0 = 1)
    (hsort : ∀ i j : A, k < i.val → k < j.val → i ≤ j → f 0 i ≤ f 0 j) :
    Spectrum.E1483.OrderTwelve.CNF.RankAssumptions f k zero := by
  letI : Magma A := ⟨f⟩
  have he : Equation1483 A := fun x y z => (h x y z).symm
  have hi (z : A) : (∃ y, f 0 y = z) ↔
      if zero then z.val < k else 0 < z.val ∧ z.val ≤ k := by
    rw [← mem_rowImage,him]
    cases zero <;> simp [targetSet]
  refine {
    source := h
    dual := CentralDual.dual he
    leftRegular := CentralDual.left_regular he
    rightRegular := CentralDual.right_regular he
    cardEq := row_col_rank f h
    minimum := hmin
    nonfull := fun x => (rank_bounds f h x).2
    rankZero := hzero
    imageZero := hi
    first := ?_
    sorted := ?_
    idemRank := idem_rank f h
    rowRank := row_edge f h
    colRank := col_edge f h }
  · cases zero
    · have hz := (hi (f 0 0)).mp ⟨0,rfl⟩
      simp only [Bool.false_eq_true, ↓reduceIte] at hz
      rcases hfirst with hfirst | hfirst
      · rw [hfirst] at hz
        simp at hz
      · exact hfirst
    · exact hfirst
  · intro y hy hy10
    have hs : (y+1).val = y.val+1 := by
      simp [Fin.val_add,Nat.mod_eq_of_lt (show y.val+1 < 12 by omega)]
    apply hsort
    · omega
    · omega
    · show y.val ≤ (y+1).val
      omega

end Spectrum.E1483.OrderTwelve.Normalized

namespace Spectrum.E1483.OrderTwelve.Normalized
open Spectrum.E1483.OrderTwelve.Normalize Spectrum.E1483.OrderTwelve.Ranks

lemma exists_normalized (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∃ k : Nat, ∃ zero : Bool, ∃ g : A → A → A,
      (2 ≤ k ∧ k < 12) ∧ Spectrum.E1483.OrderTwelve.CNF.RankAssumptions g k zero := by
  classical
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image Finset.univ (rank f)
    (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
  let k := rank f a
  have hk : 2 ≤ k ∧ k < 12 := rank_bounds f h a
  let e0 : Equiv.Perm A := Equiv.swap a 0
  let f1 := relabel f e0
  have he0 : e0.symm 0 = a := by simp [e0]
  have h1 : ∀ x y z, f1 (f1 y x) (f1 x (f1 y z)) = x := relabel_1483 f e0 h
  have h1zero : rank f1 0 = k := by rw [rank_relabel,he0]
  have h1min (x : A) : k ≤ rank f1 x := by
    rw [rank_relabel]
    exact hmin _ (Finset.mem_univ _)
  obtain ⟨zero,p,hp0,him,hfirst⟩ := exists_normal_image f1 k hk
    ((rank_image f1 0).symm.trans h1zero)
  let f2 := relabel f1 p
  have h2 : ∀ x y z, f2 (f2 y x) (f2 x (f2 y z)) = x := relabel_1483 f1 p h1
  have h2zero : rank f2 0 = k := by rw [rank_relabel,perm_symm_zero p hp0,h1zero]
  have h2min (x : A) : k ≤ rank f2 x := by rw [rank_relabel]; exact h1min _
  have hbound (x : A) (hx : x ∈ rowImage f2 0) : x.val ≤ k := by
    rw [him] at hx
    cases zero <;> simp [targetSet] at hx <;> omega
  have hf2 (x : A) : (f2 0 x).val ≤ k := hbound _ ((mem_rowImage f2 0 _).mpr ⟨x,rfl⟩)
  obtain ⟨q,hq,hsort⟩ := exists_sort_tail f2 k hf2
  have hq0 : q 0 = 0 := hq 0 (by simp)
  let f3 := relabel f2 q
  have h3 : ∀ x y z, f3 (f3 y x) (f3 x (f3 y z)) = x := relabel_1483 f2 q h2
  have h3zero : rank f3 0 = k := by rw [rank_relabel,perm_symm_zero q hq0,h2zero]
  have h3min (x : A) : k ≤ rank f3 x := by rw [rank_relabel]; exact h2min _
  have him3 : rowImage f3 0 = targetSet k zero := by
    rw [rowImage_relabel,perm_symm_zero q hq0]
    calc
      (rowImage f2 0).image q = rowImage f2 0 := by
        ext x
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨y,hy,rfl⟩
          rw [hq y (hbound y hy)]
          exact hy
        · intro hx
          exact ⟨x,hx,hq x (hbound x hx)⟩
      _ = targetSet k zero := him
  have hfirst3 : f3 0 0 = 0 ∨ f3 0 0 = 1 := by
    have hh : f3 0 0 = f2 0 0 := by
      change q (f2 (q.symm 0) (q.symm 0)) = f2 0 0
      rw [perm_symm_zero q hq0,hq _ (hf2 0)]
    rw [hh]
    exact hfirst
  exact ⟨k,zero,f3,hk,assumptions_of_normal f3 k zero h3 h3min h3zero him3 hfirst3 hsort⟩

lemma small_rank_zero_false (f : A → A → A) (k : Nat) (zero : Bool)
    (hk : k ≤ 3) (h : Spectrum.E1483.OrderTwelve.CNF.RankAssumptions f k zero) : zero = false := by
  cases zero
  · rfl
  · have hpos : 0 < k := by
      have hz := (h.imageZero (f 0 0)).mp ⟨0,rfl⟩
      change (f 0 0).val < k at hz
      omega
    obtain ⟨z,hz⟩ := (h.imageZero 0).mpr (by simpa using hpos)
    have hb := h.rowRank 0 z
    rw [hz,h.rankZero] at hb
    nlinarith

end Spectrum.E1483.OrderTwelve.Normalized

namespace Spectrum.E1483.OrderTwelve.CNF
open Magma.Central1483.CNF
lemma code12_injective : Function.Injective (@code 12) := by
  rintro ⟨atag, ax, ay, az⟩ ⟨bt, bx, by_, bz⟩ he
  have hat := atag.isLt
  have hax := ax.isLt
  have hay := ay.isLt
  have haz := az.isLt
  have hbt := bt.isLt
  have hbx := bx.isLt
  have hby := by_.isLt
  have hbz := bz.isLt
  simp only [code] at he
  ext <;> dsimp at * <;> omega

lemma no_rank_of_unsat (k : Nat) (zero : Bool) (hn : (natRankFormula 12 k zero).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : RankAssumptions f k zero) : False := by
  have hn' : (rankFormula 12 k zero).Unsat :=
    (Std.Sat.CNF.unsat_relabel_iff (fun _ _ he => code12_injective he)).mp
      (unsat_of_sanitize _ hn)
  have hh := hn' (meaning f)
  rw [model_rankFormula f k zero h] at hh
  contradiction
end Spectrum.E1483.OrderTwelve.CNF

