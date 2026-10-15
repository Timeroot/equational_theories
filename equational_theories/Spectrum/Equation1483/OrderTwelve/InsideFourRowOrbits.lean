import equational_theories.Spectrum.Equation1483.OrderTwelve.RowsData
import equational_theories.Spectrum.Equation1483.OrderTwelve.HeadLexEncoding
import equational_theories.Spectrum.Equation1483.OrderTwelve.NormalForm

/-! In the constant-head rank-four case, the three nonzero image labels can
still be permuted. The column image is forced to be `{0,4,5,6}`. Renaming the
corresponding points reduces twenty-one sorted rows to five multiplicity
patterns; sorting the second row afterwards leaves this first row intact. -/
namespace Spectrum.E1483.OrderTwelve.InsideFourRowOrbits
open Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalize Normalized Ranks Normalization RowOneNormalization HeadLexNormalization
abbrev A := Fin 12
abbrev Op := A → A → A

lemma column_eq (f : Op) (h : RankCore f 4 true) (hs : Sorted f 4 true)
    (i : Fin 21) (hr : ∀ x, f 0 x = RowsData.row i x) :
    colSet f 0 = RowsData.column := by
  have h0 : f 0 0 = 0 := (hr 0).trans (RowsData.head_zero i 0 (by decide))
  have hcol (a : A) (ha : a ∈ ([4,5,6] : List A)) : ∃ z, f z 0 = a := by
    let d := f (f 0 a) 0
    have hd : f 0 d = f 0 a := h.leftRegular 0 a
    have hdc : ∃ z, f z 0 = d := ⟨f 0 a,rfl⟩
    have had : a ≤ d := RowsData.first_occurrence i a d ha
      ((hr d).symm.trans (hd.trans (hr a)))
    have ha' : 3 < a.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl <;> decide
    have hd' : 3 < d.val := Nat.lt_of_lt_of_le ha' had
    by_contra hn
    have hk := hs a d ha' hd' had
    simp only [key,if_neg hn,if_pos hdc,hd] at hk
    omega
  have hsub : RowsData.column ⊆ colSet f 0 := by
    intro a ha
    simp only [RowsData.column,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl|rfl
    · exact (by simpa only [colSet,Finset.mem_filter,Finset.mem_univ,true_and] using
        (show ∃ z, f z 0 = 0 from ⟨0,h0⟩))
    all_goals
      simp only [colSet,Finset.mem_filter,Finset.mem_univ,true_and]
      exact hcol _ (by simp)
  have hc : (colSet f 0).card = 4 := (h.cardEq 0).trans h.rankZero
  exact (Finset.eq_of_subset_of_card_le hsub (by simpa [RowsData.column,hc])).symm

lemma relabel_core (f : Op) (h : RankCore f 4 true) (i : Fin 21)
    (hr : ∀ x, f 0 x = RowsData.row i x) :
    RankCore (relabel f (RowsData.permutation i)) 4 true := by
  let p := RowsData.permutation i
  let g := relabel f p
  have hp0 : p 0 = 0 := RowsData.zero_fixed i
  have hg := relabel_1483 f p h.source
  letI : Magma A := ⟨g⟩
  have he : Equation1483 A := fun x y z => (hg x y z).symm
  have hrow (x : A) : g 0 x = RowsData.row (RowsData.representative (RowsData.target i)) x := by
    simp only [g,relabel,perm_symm_zero p hp0,hr]
    exact RowsData.conjugates i x
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
    change 4 ≤ rank (relabel f p) x
    rw [rank_relabel]
    exact h.minimum _
  · change rank (relabel f p) 0 = 4
    rw [rank_relabel,perm_symm_zero p hp0]
    exact h.rankZero
  · intro z
    change (∃ y, g 0 y = z) ↔ z.val < 4
    simp only [hrow]
    exact RowsData.row_image _ z
  · left
    exact (hrow 0).trans (RowsData.head_zero _ 0 (by decide))

/-- Reduce the full first row to a representative, then restore the independent
second-row convention without changing any first-row entry. -/
lemma exists_representative (f : Op) (h : RankCore f 4 true) (hs : Sorted f 4 true)
    (i : Fin 21) (hr : ∀ x, f 0 x = RowsData.row i x) :
    ∃ g : Op, RankCore g 4 true ∧ Sorted g 4 true ∧ FirstMention g 4 true ∧
      ∀ x, g 0 x = RowsData.row (RowsData.representative (RowsData.target i)) x := by
  let p := RowsData.permutation i
  let g := relabel f p
  have hp0 : p 0 = 0 := RowsData.zero_fixed i
  have hg : RankCore g 4 true := relabel_core f h i hr
  have hrow (x : A) : g 0 x = RowsData.row (RowsData.representative (RowsData.target i)) x := by
    simp only [g,relabel,perm_symm_zero p hp0,hr]
    exact RowsData.conjugates i x
  have hcf (x : A) : (∃ y, f y 0 = x) ↔ x ∈ RowsData.column := by
    have hh := Finset.ext_iff.mp (column_eq f h hs i hr) x
    simpa only [colSet,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  have hcg (x : A) : (∃ y, g y 0 = x) ↔ x ∈ RowsData.column := by
    have hh : (∃ y, g y 0 = x) ↔ ∃ y, f y 0 = p.symm x := by
      simp only [g,relabel,perm_symm_zero p hp0]
      constructor
      · rintro ⟨y,hy⟩
        exact ⟨p.symm y,by simpa using congrArg p.symm hy⟩
      · rintro ⟨y,hy⟩
        exact ⟨p y,by simp [hy]⟩
    rw [hh,hcf]
    simpa [p] using (RowsData.column_preserved i (p.symm x)).symm
  have hsort : Sorted g 4 true := by
    intro a b ha hb hab
    simp only [key,hcg,hrow]
    exact RowsData.key_sorted _ a b ha hb hab
  obtain ⟨g',hg',hs',hrow',hm⟩ := refine_model g 4 true hg hsort (by decide)
  exact ⟨g',hg',hs',hm,fun x => (hrow' x).trans (hrow x)⟩

/-- Every constant head has the required head-label lexicographic symmetry. -/
lemma headLex_of_zero_head (f : Op) (h : ∀ x : A, x.val ≤ 3 → f 0 x = 0) :
    HeadLex f 4 true := by
  intro a b i ha hab hb hi hp
  have hz : (Equiv.swap a b i).val ≤ 3 := by
    simpa [bound] using swap_within a b i hab hb hi
  rw [h i hi]
  simp only [swapRow,h _ hz]
  exact Fin.zero_le _

lemma exists_normalForm (f : Op) (h : RankCore f 4 true) (hs : Sorted f 4 true)
    (i : Fin 21) (hr : ∀ x, f 0 x = RowsData.row i x) :
    ∃ g : Op, NormalForm g 4 true ∧
      ∀ x, g 0 x = RowsData.row (RowsData.representative (RowsData.target i)) x := by
  obtain ⟨g,hg,hs,hm,hr⟩ := exists_representative f h hs i hr
  have hz (x : A) (hx : x.val ≤ 3) : g 0 x = 0 :=
    (hr x).trans (RowsData.head_zero _ x hx)
  have hl := headLex_of_zero_head g hz
  refine ⟨g,⟨by decide,hg,hs,?_,fun _ => hz 1 (by decide),hl,hm⟩,hr⟩
  exact chain_of_headLex g 4 true hg hl

end Spectrum.E1483.OrderTwelve.InsideFourRowOrbits
