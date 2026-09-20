import equational_theories.Definability.Central1483SAT
import equational_theories.Definability.Central1483Translations
import equational_theories.Definability.Central1483Constant
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fin.Tuple.Sort

/-! Normalization of a hypothetical eleven-element E1483 model into the SAT rank cases. -/


set_option maxHeartbeats 1000000
namespace Magma.Central1483.Normalize

lemma swap_mem_iff {α : Type*} [DecidableEq α] (S : Set α) (a b x : α)
    (h : a ∈ S ↔ b ∈ S) : Equiv.swap a b x ∈ S ↔ x ∈ S := by
  by_cases ha : x = a
  · subst x
    simpa using h.symm
  by_cases hb : x = b
  · subst x
    simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne ha hb]

lemma exists_perm_sets_fix {α : Type*} [Fintype α] [DecidableEq α]
    (S T : Finset α) (hc : S.card = T.card) (a : α) (ha : a ∈ S ↔ a ∈ T) :
    ∃ p : Equiv.Perm α, p a = a ∧ ∀ x, p x ∈ T ↔ x ∈ S := by
  classical
  let e : S ≃ T := Classical.choice (Fintype.card_eq.mp (by simpa using hc))
  let p := e.extendSubtype
  have hp (x : α) : p x ∈ T ↔ x ∈ S := by
    constructor
    · intro hx
      by_contra hn
      exact e.extendSubtype_not_mem x hn hx
    · exact e.extendSubtype_mem x
  let q := Equiv.swap (p a) a
  refine ⟨p.trans q, ?_, ?_⟩
  · simp [q]
  · intro x
    change q (p x) ∈ T ↔ x ∈ S
    exact (swap_mem_iff (T : Set α) (p a) a (p x) ((hp a).trans ha)).trans (hp x)

lemma exists_perm_sets_fix_value {n : Nat} [NeZero n] (S T : Finset (Fin n))
    (hc : S.card = T.card) (hz : (0 : Fin n) ∈ S ↔ (0 : Fin n) ∈ T)
    (b : Fin n) (hb : b ∈ S) (h1 : (1 : Fin n) ∈ T) (hn : 2 ≤ n) :
    ∃ p : Equiv.Perm (Fin n), p 0 = 0 ∧ (∀ x, p x ∈ T ↔ x ∈ S) ∧
      (p b = 0 ∨ p b = 1) := by
  classical
  obtain ⟨p, hp0, hp⟩ := exists_perm_sets_fix S T hc 0 hz
  by_cases hpb : p b = 0
  · exact ⟨p, hp0, hp, Or.inl hpb⟩
  let q := Equiv.swap (p b) 1
  have h10 : (1 : Fin n) ≠ 0 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 1 < n by omega)]
  refine ⟨p.trans q, ?_, ?_, Or.inr ?_⟩
  · simp [q, hp0, Equiv.swap_apply_of_ne_of_ne (Ne.symm hpb) (Ne.symm h10)]
  · intro x
    change q (p x) ∈ T ↔ x ∈ S
    exact (swap_mem_iff (T : Set (Fin n)) (p b) 1 (p x)
      (by simp only [Finset.mem_coe, hp, hb, h1])).trans (hp x)
  · simp [q]

end Magma.Central1483.Normalize

namespace Magma.Central1483.Normalize

def relabel {α : Type*} (f : α → α → α) (p : Equiv.Perm α) : α → α → α :=
  fun x y => p (f (p.symm x) (p.symm y))

lemma relabel_trans {α : Type*} (f : α → α → α) (p q : Equiv.Perm α) :
    relabel (relabel f p) q = relabel f (p.trans q) := by
  funext x y
  rfl

lemma relabel_1483 {α : Type*} (f : α → α → α) (p : Equiv.Perm α)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∀ x y z, relabel f p (relabel f p y x) (relabel f p x (relabel f p y z)) = x := by
  intro x y z
  simp only [relabel, Equiv.symm_apply_apply]
  rw [h, Equiv.apply_symm_apply]

def rowImage {α : Type*} [Fintype α] [DecidableEq α] (f : α → α → α) (x : α) : Finset α :=
  Finset.univ.image (f x)

lemma mem_rowImage {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α → α) (x z : α) : z ∈ rowImage f x ↔ ∃ y, f x y = z := by
  simp [rowImage]

lemma rowImage_relabel {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α → α) (p : Equiv.Perm α) (x : α) :
    rowImage (relabel f p) x = (rowImage f (p.symm x)).image p := by
  ext z
  simp only [mem_rowImage, Finset.mem_image, relabel]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨f (p.symm x) (p.symm y), ⟨p.symm y, rfl⟩, hy⟩
  · rintro ⟨w, hw, hz⟩
    obtain ⟨y, hy⟩ := hw
    refine ⟨p y, ?_⟩
    simpa [hy] using hz

lemma card_rowImage_relabel {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α → α) (p : Equiv.Perm α) (x : α) :
    (rowImage (relabel f p) x).card = (rowImage f (p.symm x)).card := by
  rw [rowImage_relabel, Finset.card_image_of_injective _ p.injective]

end Magma.Central1483.Normalize

namespace Magma.Central1483.Normalize

def targetSet (k : Nat) (zero : Bool) : Finset (Fin 11) :=
  Finset.univ.filter fun x => if zero then x.val < k else 0 < x.val ∧ x.val ≤ k

lemma targetSet_card (k : Nat) (hk : 2 ≤ k ∧ k < 11) (zero : Bool) :
    (targetSet k zero).card = k := by
  obtain ⟨hk0, hk1⟩ := hk
  interval_cases k <;> cases zero <;> decide

lemma targetSet_zero (k : Nat) (hk : 2 ≤ k ∧ k < 11) (zero : Bool) :
    (0 : Fin 11) ∈ targetSet k zero ↔ zero = true := by
  cases zero <;> simp [targetSet] <;> omega

lemma targetSet_one (k : Nat) (hk : 2 ≤ k ∧ k < 11) (zero : Bool) :
    (1 : Fin 11) ∈ targetSet k zero := by
  cases zero <;> simp [targetSet] <;> omega

lemma exists_normal_image (f : Fin 11 → Fin 11 → Fin 11) (k : Nat)
    (hk : 2 ≤ k ∧ k < 11) (hc : (rowImage f 0).card = k) :
    ∃ zero : Bool, ∃ p : Equiv.Perm (Fin 11), p 0 = 0 ∧
      rowImage (relabel f p) 0 = targetSet k zero ∧
      (relabel f p 0 0 = 0 ∨ relabel f p 0 0 = 1) := by
  classical
  let zero := decide ((0 : Fin 11) ∈ rowImage f 0)
  have he : (0 : Fin 11) ∈ rowImage f 0 ↔ (0 : Fin 11) ∈ targetSet k zero := by
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

end Magma.Central1483.Normalize

namespace Magma.Central1483.Normalize

lemma exists_sort_tail (f : Fin 11 → Fin 11 → Fin 11) (k : Nat)
    (hf : ∀ x, (f 0 x).val ≤ k) :
    ∃ p : Equiv.Perm (Fin 11), (∀ x : Fin 11, x.val ≤ k → p x = x) ∧
      ∀ i j : Fin 11, k < i.val → k < j.val → i ≤ j →
        relabel f p 0 i ≤ relabel f p 0 j := by
  classical
  let H : Finset (Fin 11) := Finset.univ.filter (fun x => k < x.val)
  let e := H.orderIsoOfFin rfl
  let σ := Tuple.sort (fun x => f 0 (e x).val)
  let q := σ.extendDomain e.toEquiv
  have hqfix (x : Fin 11) (hx : x.val ≤ k) : q x = x := by
    apply Equiv.Perm.extendDomain_apply_not_subtype
    simpa [H] using (not_lt.mpr hx)
  have hpfix (x : Fin 11) (hx : x.val ≤ k) : q.symm x = x := by
    apply q.injective
    simpa using (hqfix x hx).symm
  refine ⟨q.symm, hpfix, ?_⟩
  have hrelabel (x : Fin 11) : relabel f q.symm 0 x = f 0 (q x) := by
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

end Magma.Central1483.Normalize

set_option maxHeartbeats 1000000
namespace Magma.Central1483.Ranks
abbrev A := Fin 11
def image (f : A → A → A) (a : A) : Finset A :=
  Finset.univ.filter (fun z => ∃ y, f a y = z)
def rank (f : A → A → A) (a : A) : Nat := (image f a).card

lemma no_constant (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ¬ ∃ a b, ∀ z, f a z = b := by
  rintro ⟨a,b,hb⟩
  letI : Magma A := ⟨f⟩
  have he : Equation1483 A := fun x y z => (h x y z).symm
  have hd := CentralConstant.even_card_of_constant_row he a b hb
    (CentralConstant.constant_values_ne he a b hb)
  norm_num [A, Nat.card_eq_fintype_card] at hd

lemma rank_bounds (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) (a : A) :
    2 ≤ rank f a ∧ rank f a < 11 := by
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
  have hle : rank f a ≤ 11 := by
    have := Finset.card_le_card (Finset.subset_univ (image f a))
    simpa [rank,A] using this
  have hne11 : rank f a ≠ 11 := by
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
    11 ≤ rank f a * rank f (f a z) := by
  letI : Magma A := ⟨f⟩
  have he : Equation1483 A := fun x y z => (h x y z).symm
  rw [rank_natCard,rank_natCard]
  simpa [A,Nat.card_eq_fintype_card] using CentralDual.row_edge_rank_bound he a z

lemma col_edge (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) (a z : A) :
    11 ≤ rank f a * rank f (f z a) := by
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

end Magma.Central1483.Ranks

namespace Magma.Central1483.Normalized
open Magma.Central1483.Normalize Magma.Central1483.Ranks
abbrev A := Fin 11

lemma rank_image (f : A → A → A) (x : A) :
    rank f x = (rowImage f x).card := by
  unfold rank
  congr 1
  ext z
  simp [image,rowImage]

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
    Magma.Central1483.CNF.RankAssumptions f k zero := by
  letI : Magma A := ⟨f⟩
  have he : Equation1483 A := fun x y z => (h x y z).symm
  have hi (z : A) : (∃ y, f 0 y = z) ↔
      if zero then z.val < k else 0 < z.val ∧ z.val ≤ k := by
    rw [← mem_rowImage,him]
    cases zero <;> simp [targetSet]
  refine ⟨h, CentralDual.dual he, CentralDual.left_regular he,
    CentralDual.right_regular he, row_col_rank f h, hmin,
    fun x => (rank_bounds f h x).2, hzero, hi, ?_, ?_, idem_rank f h,
    row_edge f h, col_edge f h⟩
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
      simp [Fin.val_add,Nat.mod_eq_of_lt (show y.val+1 < 11 by omega)]
    apply hsort
    · omega
    · omega
    · show y.val ≤ (y+1).val
      omega

end Magma.Central1483.Normalized

namespace Magma.Central1483.Normalized
open Magma.Central1483.Normalize Magma.Central1483.Ranks

lemma exists_normalized (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∃ k : Nat, ∃ zero : Bool, ∃ g : A → A → A,
      (2 ≤ k ∧ k < 11) ∧ Magma.Central1483.CNF.RankAssumptions g k zero := by
  classical
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image Finset.univ (rank f)
    (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
  let k := rank f a
  have hk : 2 ≤ k ∧ k < 11 := rank_bounds f h a
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
    (hk : k ≤ 3) (h : Magma.Central1483.CNF.RankAssumptions f k zero) : zero = false := by
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

end Magma.Central1483.Normalized

namespace Magma.Central1483.CNF
lemma code11_injective : Function.Injective (@code 11) := by
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

lemma no_rank_of_unsat (k : Nat) (zero : Bool) (hn : (natRankFormula 11 k zero).Unsat)
    (f : Fin 11 → Fin 11 → Fin 11) (h : RankAssumptions f k zero) : False := by
  have hn' : (rankFormula 11 k zero).Unsat :=
    (Std.Sat.CNF.unsat_relabel_iff (fun _ _ he => code11_injective he)).mp
      (unsat_of_sanitize _ hn)
  have hh := hn' (meaning f)
  rw [model_rankFormula f k zero h] at hh
  contradiction
end Magma.Central1483.CNF

/-- info: 'Magma.Central1483.Normalized.exists_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Magma.Central1483.Normalized.exists_normalized

/-- info: 'Magma.Central1483.Normalized.small_rank_zero_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Magma.Central1483.Normalized.small_rank_zero_false

/-- info: 'Magma.Central1483.CNF.no_rank_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Magma.Central1483.CNF.no_rank_of_unsat
