import equational_theories.Spectrum.PBD.MarkedTruncation
import equational_theories.Spectrum.PBD.UniformSeeds

/-! The six ingredients used to extend arithmetic progressions. The large
auxiliary design only needs a marked block; no general cyclotomic existence
theorem is needed to construct it. -/
namespace Spectrum.PBD
open Classical PairDecomposition

/-- Arbitrarily large designs containing one prescribed permitted block.
The adjacent block size is available in the applications below. -/
theorem unbounded_marked {C : Set ℕ} (_hC : DesignClosed C) {b : ℕ}
    (hb : 0 < b) (hbC : b ∈ C) (hbC' : b+1 ∈ C)
    (hu : ∀ N, ∃ q, N ≤ q ∧ q ∈ C) :
    ∀ N, ∃ h, N ≤ h ∧ HasBlockDesign C h b := by
  intro N
  obtain ⟨A,hA⟩ := HasTD.eventual (b+1)
  obtain ⟨q,hq,hqC⟩ := hu (A+N+1)
  obtain ⟨T⟩ := hA q (by omega)
  let T' := T.reindex (finSuccEquiv b).symm
  let F : Complete C (Fin q) := singleBlock (by simpa using hqC)
  let P : Complete C (Fin 0) := PairDecomposition.empty
  let D := MarkedTruncation.design T' (r := 0) (by omega) hbC hbC' F P
  have h := MarkedTruncation.contains_short_line T' (r := 0) (by omega) hbC hbC' F P hb (by omega)
  refine ⟨b*q,by nlinarith,?_⟩
  exact hasBlockDesign_of_card h (by simpa using MarkedTruncation.card_points (k := b) (r := 0) (by omega : 0 ≤ q))

/-- Wilson's six local group types. Besides the two complete orders, the
four holes have outside orders `H,H+1` and hole orders `a,b`. -/
theorem six_hole_ingredients {C : Set ℕ} (hC : DesignClosed C) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (haC : a ∈ C) (haC' : a+1 ∈ C) (hbC : b ∈ C) (hbC' : b+1 ∈ C)
    (hu : ∀ N, ∃ q, N ≤ q ∧ q ∈ C) :
    ∃ h, 0 < h ∧ a*h ∈ C ∧ a*h+1 ∈ C ∧
      HasHole C a (a*h) ∧ HasHole C a (a*h+1) ∧
      HasHole C b (a*h) ∧ HasHole C b (a*h+1) := by
  obtain ⟨A,hA⟩ := HasTD.eventual (a+1)
  obtain ⟨h,hh,hmarked⟩ := unbounded_marked hC hb hbC hbC' hu (A+a+b+2)
  have hhC : h ∈ C := hC hmarked.mem_closure
  obtain ⟨T⟩ := hA h (by omega)
  let T' := T.reindex (finSuccEquiv a).symm
  let F : Complete C (Fin h) := hmarked.choose
  have hF : F.ContainsBlock b := hmarked.choose_spec
  have hzero : a*h ∈ C := by
    have h := hC.oneHole ⟨T⟩ (e := 0) (r := 0) (by omega) (by omega)
      (by simpa using hhC) (by simpa using hC.zero_mem) haC haC'
    simpa using h
  have hone : a*h+1 ∈ C := by
    have h := hC.oneHole ⟨T⟩ (e := 0) (r := 1) (by omega) (by omega)
      (by simpa using hhC) (by simpa using hC.one_mem) haC haC'
    simpa using h
  have hole_part (r : ℕ) (hr : r ≤ h) (hrC : r ∈ C) : HasHole C r (a*h) := by
    let P : Complete C (Fin r) := singleBlock (by simpa using hrC)
    have hP : P.ContainsBlock r := by simpa using singleBlock_contains (X := Fin r) (by simpa using hrC)
    have hm := MarkedTruncation.contains_part T' hr haC haC' F P hP
    exact (hasBlockDesign_of_card hm (MarkedTruncation.card_points hr)).hole (by omega)
  have hole_a : HasHole C a (a*h+1) := by
    let P : Complete C (Fin (a+1)) := singleBlock (by simpa using haC')
    have hm := MarkedTruncation.contains_short_line T' (r := a+1) (by omega) haC haC' F P ha (by omega)
    exact (hasBlockDesign_of_card hm (MarkedTruncation.card_points (by omega : a+1 ≤ h))).hole (by omega)
  have hole_b : HasHole C b (a*h+1) := by
    let P : Complete C (Fin (b+1)) := singleBlock (by simpa using hbC')
    have hm := MarkedTruncation.contains_full T' (r := b+1) (by omega) haC haC' F P ha hF
    exact (hasBlockDesign_of_card hm (MarkedTruncation.card_points (by omega : b+1 ≤ h))).hole (by omega)
  exact ⟨h,by omega,hzero,hone,hole_part a (by omega) haC,hole_a,
    hole_part b (by omega) hbC,hole_b⟩

end Spectrum.PBD
