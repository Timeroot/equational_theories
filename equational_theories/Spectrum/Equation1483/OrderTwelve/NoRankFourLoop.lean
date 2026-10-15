import equational_theories.Spectrum.Equation1483.OrderTwelve.InsideFourExclusion

/-! The rank-four inside exclusion can be used at every point of a model, not
only at the initially distinguished minimum-rank row. Move a rank-four loop
to zero, normalize its image, and retain that pivot through all refinements. -/
namespace Spectrum.E1483.OrderTwelve.NoRankFourLoop
open Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalize Normalized Ranks Normalization HeadLexNormalization RowOneNormalization
abbrev A := Fin 12
abbrev Op := A → A → A

lemma normalForm_of_core (f : Op) (k : Nat) (zero : Bool)
    (hk : 2 ≤ k ∧ k < 12) (h : RankCore f k zero) :
    ∃ g : Op, NormalForm g k zero := by
  obtain ⟨g,hg,hI⟩ := IdempotentNormalization.choose_predecessor f k zero hk.1 h
  obtain ⟨g,hg,hI,hl⟩ := exists_head_minimal g k zero hg hI
  obtain ⟨q,hq,hs,hr⟩ := exists_sorted g k zero hg
  have hlex : HeadLex q k zero := head_congr g q k zero hl hr
  have hqI : q 0 0 = 0 → q 0 1 = 0 := by
    intro hz
    have h1 : (1 : A).val ≤ bound k zero := by cases zero <;> simp [bound] <;> omega
    rw [hr 1 h1]
    exact hI ((hr 0 (by simp)).symm.trans hz)
  obtain ⟨q',hq',hs',hr',hm⟩ := refine_model q k zero hq hs hk.1
  have hlex' : HeadLex q' k zero := head_congr q q' k zero hlex (fun x _ => hr' x)
  refine ⟨q',hk,hq',hs',chain_of_headLex q' k zero hq' hlex',?_,hlex',hm⟩
  intro hz
  rw [hr' 1]
  exact hqI ((hr' 0).symm.trans hz)

lemma pivot_core (f : Op) (h : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (hmin : ∀ x, 4 ≤ rowSize f x) (a : A) (ha : rowSize f a = 4)
    (hloop : ∃ z, f a z = a) : ∃ g : Op, RankCore g 4 true := by
  let e : Equiv.Perm A := Equiv.swap a 0
  let f₁ := relabel f e
  have he : e.symm 0 = a := by simp [e]
  have h₁ := relabel_1483 f e h
  have hz₁ : rank f₁ 0 = 4 := by rw [rank_relabel,he]; exact ha
  have hm₁ (x : A) : 4 ≤ rank f₁ x := by rw [rank_relabel]; exact hmin _
  have hl₁ : (0 : A) ∈ rowImage f₁ 0 := by
    obtain ⟨z,hz⟩ := hloop
    apply (mem_rowImage f₁ 0 0).mpr
    refine ⟨e z,?_⟩
    simp only [f₁,relabel,he,e.symm_apply_apply,hz]
    simp [e]
  obtain ⟨zero,p,hp0,him,hfirst⟩ := exists_normal_image f₁ 4 (by decide)
    ((rank_image f₁ 0).symm.trans hz₁)
  let g := relabel f₁ p
  have hg := relabel_1483 f₁ p h₁
  have hl₂ : (0 : A) ∈ rowImage g 0 := by
    rw [rowImage_relabel,perm_symm_zero p hp0]
    exact Finset.mem_image.mpr ⟨0,hl₁,hp0⟩
  have hzero : zero = true := (targetSet_zero 4 (by decide) zero).mp (him ▸ hl₂)
  subst zero
  letI : Magma A := ⟨g⟩
  have hE : Equation1483 A := fun x y z => (hg x y z).symm
  refine ⟨g,{
    source := hg
    dual := CentralDual.dual hE
    leftRegular := CentralDual.left_regular hE
    rightRegular := CentralDual.right_regular hE
    cardEq := row_col_rank g hg
    minimum := ?_
    nonfull := fun x => (rank_bounds g hg x).2
    rankZero := ?_
    imageZero := ?_
    first := hfirst
    idemRank := idem_rank g hg
    rowRank := row_edge g hg
    colRank := col_edge g hg }⟩
  · intro x
    change 4 ≤ rank (relabel f₁ p) x
    rw [rank_relabel]
    exact hm₁ _
  · change rank (relabel f₁ p) 0 = 4
    rw [rank_relabel,perm_symm_zero p hp0,hz₁]
  · intro z
    rw [← mem_rowImage,him]
    simp [targetSet]

/-- At order twelve, a loop cannot occur at a minimum-rank-four vertex. -/
lemma loop_rank_ge_five (f : Op)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (hmin : ∀ x, 4 ≤ rowSize f x) (a : A) (hloop : ∃ z, f a z = a) :
    5 ≤ rowSize f a := by
  by_contra hn
  have ha : rowSize f a = 4 := by have := hmin a; omega
  obtain ⟨g,hg⟩ := pivot_core f h hmin a ha hloop
  obtain ⟨q,hq⟩ := normalForm_of_core g 4 true (by decide) hg
  exact InsideFourExclusion.no_model q hq

lemma of_normalForm (f : Op) (h : NormalForm f 4 false)
    (a : A) (hloop : ∃ z, f a z = a) : 5 ≤ rowSize f a :=
  loop_rank_ge_five f h.core.source h.core.minimum a hloop

end Spectrum.E1483.OrderTwelve.NoRankFourLoop
