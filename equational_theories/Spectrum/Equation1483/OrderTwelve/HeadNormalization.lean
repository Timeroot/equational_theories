import equational_theories.Spectrum.Equation1483.OrderTwelve.Normalization

/-! Normalize the whole row-image head, before sorting the complementary labels. -/
namespace Spectrum.E1483.OrderTwelve.HeadNormalization
open Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalize Normalized Ranks Normalization
abbrev A := Fin 12

/-- Greedy traversal stays inside a bounded image. Thus the remaining labels
can subsequently be sorted without disturbing this normalization. -/
theorem chain_bounded (f : A → A) (b : Nat)
    (hb : ∀ x, (f x).val ≤ b) (hzero : (f 0).val ≤ 1) :
    ∃ e : Equiv.Perm A, (∀ i, i.val ≤ 1 → e i = i) ∧
      (∀ i, b < i.val → e i = i) ∧
      ∀ i, (e (f (e.symm i))).val ≤ i.val + 1 := by
  classical
  have aux (t : Nat) : ∃ e : Equiv.Perm A, (∀ i, i.val ≤ 1 → e i = i) ∧
      (∀ i, b < i.val → e i = i) ∧
      ∀ i, i.val < 1+t → (e (f (e.symm i))).val ≤ i.val+1 := by
    induction t with
    | zero =>
      refine ⟨Equiv.refl _, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
      intro i hi
      have hz : i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      subst i
      exact hzero
    | succ t ih =>
      obtain ⟨e, he, htail, hf⟩ := ih
      let k := 1+t
      by_cases hk : k < 12
      · let i : A := ⟨k,hk⟩
        let g (j : A) := e (f (e.symm j))
        have hg (j : A) : (g j).val ≤ b := by
          by_contra hh
          have hx := htail (g j) (by omega)
          have hy : g j = f (e.symm j) := e.injective hx
          have hz := hb (e.symm j)
          rw [hy] at hh
          omega
        by_cases hi : (g i).val ≤ k+1
        · refine ⟨e,he,htail, fun j hj => ?_⟩
          by_cases hjk : j.val < k
          · exact hf j hjk
          · have hji : j = i := Fin.ext (by dsimp [i,k] at *; omega)
            subst j
            exact hi
        · have ha : k+1 < 12 := by have := (g i).isLt; omega
          let a : A := ⟨k+1,ha⟩
          let s := Equiv.swap a (g i)
          have fixed (j : A) (hj : j.val < k+1) : s j = j := by
            apply Equiv.swap_apply_of_ne_of_ne <;> intro hh
            · have := congrArg Fin.val hh; dsimp [a] at this; omega
            · have := congrArg Fin.val hh; omega
          refine ⟨e.trans s, ?_, ?_, fun j hj => ?_⟩
          · intro j hj
            change s (e j) = j
            rw [he j hj, fixed j (by dsimp [k]; omega)]
          · intro j hj
            change s (e j) = j
            rw [htail j hj]
            apply Equiv.swap_apply_of_ne_of_ne <;> intro hh
            · have hh' := congrArg Fin.val hh
              have hgi := hg i
              dsimp [a] at hh'
              omega
            · have hh' := congrArg Fin.val hh
              have hgi := hg i
              omega
          · change (s (g (s j))).val ≤ j.val+1
            rw [fixed j (by dsimp [k] at *; omega)]
            by_cases hjk : j.val < k
            · rw [fixed (g j) (by have := hf j hjk; change (g j).val ≤ j.val+1 at this; omega)]
              exact hf j hjk
            · have hji : j = i := Fin.ext (by dsimp [i,k] at *; omega)
              subst j
              change (Equiv.swap a (g i) (g i)).val ≤ k+1
              rw [Equiv.swap_apply_right]
      · exact ⟨e,he,htail,fun j _ => hf j (by have := j.isLt; dsimp [k] at *; omega)⟩
  obtain ⟨e,he,ht,hf⟩ := aux 12
  exact ⟨e,he,ht,fun i => hf i (by have := i.isLt; omega)⟩

lemma core_relabel_image (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (p : Equiv.Perm A)
    (hp0 : p 0 = 0) (hp1 : p 1 = 1)
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
  · have hf := h.first
    change (if zero then g 0 0 = 0 ∨ g 0 0 = 1 else g 0 0 = 1)
    have h00 : g 0 0 = p (f 0 0) := by simp [g,relabel,perm_symm_zero p hp0]
    rw [h00]
    cases zero
    · simp only [Bool.false_eq_true,↓reduceIte] at hf ⊢
      rw [hf,hp1]
    · simp only [↓reduceIte] at hf ⊢
      rcases hf with hf|hf <;> simp [hf,hp0,hp1]

lemma exists_normalized (f : A → A → A)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∃ k : Nat, ∃ zero : Bool, ∃ g : A → A → A,
      (2 ≤ k ∧ k < 12) ∧ RankCore g k zero ∧ Sorted g k zero ∧
      (∀ y, (g 0 y).val ≤ y.val+1) := by
  obtain ⟨k,zero,g,hk,hg⟩ := Normalized.exists_normalized f h
  have hzero : (g 0 0).val ≤ 1 := by
    have hh := hg.first
    cases zero <;> simp_all
    rcases hh with hh|hh <;> simp [hh]
  obtain ⟨p,hp,ht,hc⟩ := chain_bounded (g 0) (bound k zero)
    (output_bound g k zero hg.toRankCore) hzero
  have hp0 : p 0 = 0 := hp 0 (by decide)
  have hh := core_relabel_image g k zero hg.toRankCore p hp0 (hp 1 (by decide)) ht
  obtain ⟨g',hg',hs,hrow⟩ := exists_sorted (relabel g p) k zero hh
  refine ⟨k,zero,g',hk,hg',hs,?_⟩
  intro y
  by_cases hy : y.val ≤ bound k zero
  · rw [hrow y hy]
    simpa only [relabel,perm_symm_zero p hp0] using hc y
  · have hb := output_bound g' k zero hg' y
    omega

end Spectrum.E1483.OrderTwelve.HeadNormalization
