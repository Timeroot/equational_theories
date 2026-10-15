import equational_theories.Spectrum.Equation1483.OrderEleven.Encoding

/-!
# Normalize both translation images

The translations at zero restrict to inverse bijections on their images.
After fixing the row image, sort the other points by column-image membership
first, and then by row-zero output. Column-image points therefore receive
consecutive labels in the order of their inverse images. The remaining points
are sorted within row fibers. This replaces the old sorting convention.
-/
namespace Spectrum.E1483.OrderEleven.Normalization
open Magma.Central1483.CNF Magma.Central1483.Normalize
open Magma.Central1483.Normalized Magma.Central1483.Ranks
abbrev A := Fin 11

def bound (k : Nat) (zero : Bool) : Nat := if zero then k-1 else k

def key (f : A → A → A) (x : A) : Nat :=
  if ∃ y, f y 0 = x then (f 0 x).val else 11 + (f 0 x).val

def Sorted (f : A → A → A) (k : Nat) (zero : Bool) : Prop :=
  ∀ i j : A, bound k zero < i.val → bound k zero < j.val → i ≤ j →
    key f i ≤ key f j

lemma output_bound (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (x : A) : (f 0 x).val ≤ bound k zero := by
  have hx := (h.imageZero (f 0 x)).mp ⟨x,rfl⟩
  cases zero <;> simp only [bound, Bool.false_eq_true,
    ↓reduceIte] at * <;> omega

lemma row_relabel (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (p : Equiv.Perm A)
    (hp : ∀ x : A, x.val ≤ bound k zero → p x = x) (x : A) :
    relabel f p 0 x = f 0 (p.symm x) := by
  have hp0 : p 0 = 0 := hp 0 (Nat.zero_le _)
  simp only [relabel, perm_symm_zero p hp0]
  exact hp _ (output_bound f k zero h _)

lemma key_relabel (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (p : Equiv.Perm A)
    (hp : ∀ x : A, x.val ≤ bound k zero → p x = x) (x : A) :
    key (relabel f p) x = key f (p.symm x) := by
  have hp0 : p 0 = 0 := hp 0 (Nat.zero_le _)
  have hc : (∃ y, relabel f p y 0 = x) ↔ ∃ y, f y 0 = p.symm x := by
    simp only [relabel, perm_symm_zero p hp0]
    constructor
    · rintro ⟨y,hy⟩
      exact ⟨p.symm y, by simpa using congrArg p.symm hy⟩
    · rintro ⟨y,hy⟩
      refine ⟨p y, ?_⟩
      simp [hy]
  simp only [key, hc, row_relabel f k zero h p hp]

lemma core_relabel (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (p : Equiv.Perm A)
    (hp : ∀ x : A, x.val ≤ bound k zero → p x = x) :
    RankCore (relabel f p) k zero := by
  let g := relabel f p
  have hp0 : p 0 = 0 := hp 0 (Nat.zero_le _)
  have hg := relabel_1483 f p h.source
  letI : Magma A := ⟨g⟩
  have he : Equation1483 A := fun x y z => (hg x y z).symm
  have h0 : g 0 0 = f 0 0 := by
    change relabel f p 0 0 = f 0 0
    rw [row_relabel f k zero h p hp, perm_symm_zero p hp0]
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
    rw [rank_relabel, perm_symm_zero p hp0]
    exact h.rankZero
  · intro z
    rw [← h.imageZero z]
    constructor
    · rintro ⟨y,hy⟩
      exact ⟨p.symm y, (row_relabel f k zero h p hp y).symm.trans hy⟩
    · rintro ⟨y,hy⟩
      exact ⟨p y, by simpa [row_relabel f k zero h p hp] using hy⟩
  · change (if zero then g 0 0 = 0 ∨ g 0 0 = 1 else g 0 0 = 1)
    rw [h0]
    exact h.first

/-- The first new value after `0 * 0 = 1` can always be named `2`.
This permutation stays inside the already normalized row image. -/
lemma exists_first_two (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) :
    ∃ g : A → A → A, RankCore g k zero ∧ (g 0 1).val ≤ 2 := by
  classical
  by_cases ht : (f 0 1).val ≤ 2
  · exact ⟨f,h,ht⟩
  let t := f 0 1
  change ¬ t.val ≤ 2 at ht
  have ht2 : t ≠ 2 := by intro he; simp [he] at ht
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht
  have ht1 : t ≠ 1 := by intro he; simp [he] at ht
  let p := Equiv.swap (2 : A) t
  have hp0 : p 0 = 0 := by simp [p,Equiv.swap_apply_of_ne_of_ne,ht0.symm]
  have hp1 : p 1 = 1 := by simp [p,Equiv.swap_apply_of_ne_of_ne,ht1.symm]
  have htI := (h.imageZero t).mp ⟨1,rfl⟩
  have hperm (z : A) :
      (if zero then (p z).val < k else 1 ≤ (p z).val ∧ (p z).val ≤ k) ↔
      (if zero then z.val < k else 1 ≤ z.val ∧ z.val ≤ k) := by
    by_cases hz : z = 2
    · subst z; simp only [p,Equiv.swap_apply_left]
      cases zero <;> simp_all <;> omega
    by_cases hz' : z = t
    · subst z; simp only [p,Equiv.swap_apply_right]
      cases zero <;> simp_all <;> omega
    simp only [p,Equiv.swap_apply_of_ne_of_ne hz hz']
  let g := relabel f p
  have hg := relabel_1483 f p h.source
  letI : Magma A := ⟨g⟩
  have he : Equation1483 A := fun x y z => (hg x y z).symm
  have hg00 : g 0 0 = f 0 0 := by
    change p (f (p.symm 0) (p.symm 0)) = f 0 0
    rw [perm_symm_zero p hp0]
    have hf := h.first
    cases zero
    · simp only [Bool.false_eq_true,↓reduceIte] at hf
      rw [hf,hp1]
    · simp only [↓reduceIte] at hf
      rcases hf with hf|hf <;> simp only [hf,hp0,hp1]
  refine ⟨g,?_,?_⟩
  · refine {
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
      have him : (∃ y, g 0 y = z) ↔ ∃ y, f 0 y = p z := by
        simp only [g,relabel,perm_symm_zero p hp0]
        constructor
        · rintro ⟨y,hy⟩
          exact ⟨p.symm y, by simpa [p] using congrArg p hy⟩
        · rintro ⟨y,hy⟩
          exact ⟨p y, by simpa [p] using congrArg p hy⟩
      exact him.trans ((h.imageZero (p z)).trans (hperm z))
    · change (if zero then g 0 0 = 0 ∨ g 0 0 = 1 else g 0 0 = 1)
      rw [hg00]
      exact h.first
  · have hp1' : p.symm 1 = 1 := by apply p.injective; simpa using hp1.symm
    change (p (f (p.symm 0) (p.symm 1))).val ≤ 2
    rw [perm_symm_zero p hp0,hp1']
    simp [p,← show t = f 0 1 from rfl]

lemma exists_sorted (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) :
    ∃ g : A → A → A, RankCore g k zero ∧ Sorted g k zero ∧
      (∀ x : A, x.val ≤ bound k zero → g 0 x = f 0 x) := by
  classical
  let H : Finset A := Finset.univ.filter (fun x => bound k zero < x.val)
  let e := H.orderIsoOfFin rfl
  let σ := Tuple.sort (fun x => key f (e x).val)
  let q := σ.extendDomain e.toEquiv
  have hqfix (x : A) (hx : x.val ≤ bound k zero) : q x = x := by
    apply Equiv.Perm.extendDomain_apply_not_subtype
    simpa [H] using (not_lt.mpr hx)
  have hpfix (x : A) (hx : x.val ≤ bound k zero) : q.symm x = x := by
    apply q.injective
    simpa using (hqfix x hx).symm
  refine ⟨relabel f q.symm, core_relabel f k zero h q.symm hpfix, ?_, ?_⟩
  swap
  · intro x hx
    rw [row_relabel f k zero h q.symm hpfix]
    simp only [Equiv.symm_symm,hqfix x hx]
  intro i j hi hj hij
  rw [key_relabel f k zero h q.symm hpfix, key_relabel f k zero h q.symm hpfix]
  simp only [Equiv.symm_symm]
  have hiH : i ∈ H := by simpa [H] using hi
  have hjH : j ∈ H := by simpa [H] using hj
  have hiq : q i = e (σ (e.symm ⟨i,hiH⟩)) :=
    Equiv.Perm.extendDomain_apply_subtype σ e.toEquiv hiH
  have hjq : q j = e (σ (e.symm ⟨j,hjH⟩)) :=
    Equiv.Perm.extendDomain_apply_subtype σ e.toEquiv hjH
  rw [hiq,hjq]
  exact Tuple.monotone_sort (fun x => key f (e x).val) (e.symm.monotone hij)

lemma exists_normalized (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∃ k : Nat, ∃ zero : Bool, ∃ g : A → A → A,
      (2 ≤ k ∧ k < 11) ∧ RankCore g k zero ∧ Sorted g k zero ∧ (g 0 1).val ≤ 2 := by
  obtain ⟨k,zero,g,hk,hg⟩ := Magma.Central1483.Normalized.exists_normalized f h
  obtain ⟨g₁,hg₁,ht⟩ := exists_first_two g k zero hg.toRankCore
  obtain ⟨g',hg',hs,hrow⟩ := exists_sorted g₁ k zero hg₁
  have h1 : (1 : A).val ≤ bound k zero := by cases zero <;> simp [bound] <;> omega
  exact ⟨k,zero,g',hk,hg',hs,by simpa [hrow 1 h1] using ht⟩

end Spectrum.E1483.OrderEleven.Normalization
