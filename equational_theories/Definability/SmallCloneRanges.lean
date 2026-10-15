import equational_theories.Definability.Clone
import equational_theories.Definability.Invariant
import equational_theories.Definability.FiniteFlavour
import equational_theories.Equations.All
import Mathlib.Tactic.FinCases

/-! Recovery obstructions from three six-element magmas with small binary clones.
Every target companion is a projection or has its image in a fixed small set.
Term composition preserves that alternative, whereas the source fails it. -/
open Law Law.MagmaLaw
namespace SmallCloneRanges

def ProjectionOrRange {G : Type} (S : Set G) (f : G → G → G) : Prop :=
  (∀ x y, f x y = x) ∨ (∀ x y, f x y = y) ∨ ∀ x y, f x y ∈ S
instance {G : Type} [Fintype G] [DecidableEq G] (S : Set G) [DecidablePred (· ∈ S)]
    (f : G → G → G) : Decidable (ProjectionOrRange S f) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem invariant {G : Type} (S : Set G) (N : Magma G)
    (h : ProjectionOrRange S N.op) : N.IsCloneInvariant (ProjectionOrRange S) where
  fst := Or.inl (fun _ _ => rfl)
  snd := Or.inr (Or.inl (fun _ _ => rfl))
  comp := by
    intro f g hf hg
    rcases h with hl | hr | hs
    · simpa only [hl] using hf
    · simpa only [hr] using hg
    · exact Or.inr (Or.inr (fun x y => hs (f x y) (g x y)))

theorem obstruct {G : Type} [Finite G] {L A : NatMagmaLaw} (M : Magma G)
    (hM : @satisfies _ G M A) {I : Type} (C : I → Magma G) {i₁ i₂ comp}
    (hc : M.IsCloneFamily C i₁ i₂ comp) (S : Set G)
    (hm : ¬ ProjectionOrRange S M.op)
    (ht : ∀ i, @satisfies _ G (C i) L → ProjectionOrRange S (C i).op) :
    ¬ L.TermStructuralFromFin A := by
  intro h
  obtain ⟨N,hn,hf,hr⟩ := h M hM
  obtain ⟨i,rfl⟩ := hc.exists_eq hf
  exact hm ((invariant S (C i) (ht i hn)).of_termDefinable hr)

abbrev Point := Fin 6

namespace Model27
def table : Fin 4 → Point → Point → Point :=
  ![![![0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2], ![3, 3, 3, 3, 3, 3], ![4, 4, 4, 4, 4, 4], ![5, 5, 5, 5, 5, 5]],
    ![![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5]],
    ![![0, 5, 5, 3, 5, 5], ![3, 1, 4, 3, 4, 5], ![3, 4, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![5, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5]],
    ![![0, 3, 3, 0, 5, 0], ![5, 1, 4, 1, 1, 1], ![5, 4, 2, 2, 2, 2], ![3, 3, 3, 3, 3, 3], ![5, 4, 4, 4, 4, 4], ![5, 5, 5, 5, 5, 5]]]
@[implicit_reducible] def family (i : Fin 4) : Magma Point := ⟨table i⟩
@[implicit_reducible] def source : Magma Point := family 3
def compose : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 3, 0, 0],
    ![2, 1, 1, 1],
    ![2, 2, 2, 2],
    ![3, 3, 3, 3]]
theorem closed : source.IsCloneFamily family 0 1 compose where
  fst := by decide
  snd := by decide
  comp := by decide +kernel
theorem source_law : @Equation1037 Point source := by decide
def support : Set Point := {}
instance : DecidablePred (· ∈ support) := by unfold support; infer_instance
theorem source_outside : ¬ ProjectionOrRange support source.op := by decide
def bad : Fin 2 → Fin 4 := ![2, 3]
theorem coverage : ∀ i, ProjectionOrRange support (family i).op ∨ ∃ j, i = bad j := by decide

private theorem exclude3529 : ∀ j, ¬ @Equation3529 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 1 0 2)
  · exact (by decide : (3 : Point) ≠ 0) (h 0 1 0)

theorem Equation3529_not_termStructuralFromFin_Equation1037 : ¬ Law3529.TermStructuralFromFin Law1037 := by
  apply obstruct source ((@Law1037.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude3529 j ((@Law3529.models_iff Point (family (bad j))).mp hi))

end Model27

namespace Model6
def table : Fin 9 → Point → Point → Point :=
  ![![![0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2], ![3, 3, 3, 3, 3, 3], ![4, 4, 4, 4, 4, 4], ![5, 5, 5, 5, 5, 5]],
    ![![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5]],
    ![![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5]],
    ![![3, 4, 5, 5, 3, 5], ![2, 3, 5, 5, 5, 5], ![3, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5]],
    ![![3, 2, 3, 5, 5, 5], ![4, 3, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![3, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5]],
    ![![3, 3, 5, 5, 5, 5], ![3, 3, 5, 5, 5, 5], ![3, 3, 5, 5, 5, 5], ![3, 3, 5, 5, 5, 5], ![3, 3, 5, 5, 5, 5], ![3, 3, 5, 5, 5, 5]],
    ![![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5]],
    ![![5, 3, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5]],
    ![![5, 5, 5, 5, 5, 5], ![3, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5], ![5, 5, 5, 5, 5, 5]]]
@[implicit_reducible] def family (i : Fin 9) : Magma Point := ⟨table i⟩
@[implicit_reducible] def source : Magma Point := family 4
def compose : Fin 9 → Fin 9 → Fin 9 :=
  ![![2, 4, 6, 6, 7, 6, 6, 6, 6],
    ![3, 5, 6, 8, 6, 6, 6, 6, 6],
    ![6, 6, 6, 6, 6, 6, 6, 6, 6],
    ![7, 6, 6, 6, 6, 6, 6, 6, 6],
    ![6, 8, 6, 6, 6, 6, 6, 6, 6],
    ![6, 6, 6, 6, 6, 6, 6, 6, 6],
    ![6, 6, 6, 6, 6, 6, 6, 6, 6],
    ![6, 6, 6, 6, 6, 6, 6, 6, 6],
    ![6, 6, 6, 6, 6, 6, 6, 6, 6]]
theorem closed : source.IsCloneFamily family 0 1 compose where
  fst := by decide
  snd := by decide
  comp := by decide +kernel
theorem source_law : @Equation4541 Point source := by decide
def support : Set Point := {3, 5}
instance : DecidablePred (· ∈ support) := by unfold support; infer_instance
theorem source_outside : ¬ ProjectionOrRange support source.op := by decide
def bad : Fin 2 → Fin 9 := ![3, 4]
theorem coverage : ∀ i, ProjectionOrRange support (family i).op ∨ ∃ j, i = bad j := by decide

private theorem exclude4512 : ∀ j, ¬ @Equation4512 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)

theorem Equation4512_not_termStructuralFromFin_Equation4541 : ¬ Law4512.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4512 j ((@Law4512.models_iff Point (family (bad j))).mp hi))

private theorem exclude4290 : ∀ j, ¬ @Equation4290 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)

theorem Equation4290_not_termStructuralFromFin_Equation4541 : ¬ Law4290.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4290 j ((@Law4290.models_iff Point (family (bad j))).mp hi))

private theorem exclude4515 : ∀ j, ¬ @Equation4515 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)

theorem Equation4515_not_termStructuralFromFin_Equation4541 : ¬ Law4515.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4515 j ((@Law4515.models_iff Point (family (bad j))).mp hi))

private theorem exclude4358 : ∀ j, ¬ @Equation4358 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)

theorem Equation4358_not_termStructuralFromFin_Equation4541 : ¬ Law4358.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4358 j ((@Law4358.models_iff Point (family (bad j))).mp hi))

private theorem exclude4364 : ∀ j, ¬ @Equation4364 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)

theorem Equation4364_not_termStructuralFromFin_Equation4541 : ¬ Law4364.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4364 j ((@Law4364.models_iff Point (family (bad j))).mp hi))

private theorem exclude4396 : ∀ j, ¬ @Equation4396 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)

theorem Equation4396_not_termStructuralFromFin_Equation4541 : ¬ Law4396.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4396 j ((@Law4396.models_iff Point (family (bad j))).mp hi))

private theorem exclude4398 : ∀ j, ¬ @Equation4398 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)

theorem Equation4398_not_termStructuralFromFin_Equation4541 : ¬ Law4398.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4398 j ((@Law4398.models_iff Point (family (bad j))).mp hi))

private theorem exclude4369 : ∀ j, ¬ @Equation4369 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)

theorem Equation4369_not_termStructuralFromFin_Equation4541 : ¬ Law4369.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4369 j ((@Law4369.models_iff Point (family (bad j))).mp hi))

private theorem exclude4531 : ∀ j, ¬ @Equation4531 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 0 1)

theorem Equation4531_not_termStructuralFromFin_Equation4541 : ¬ Law4531.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4531 j ((@Law4531.models_iff Point (family (bad j))).mp hi))

private theorem exclude4283 : ∀ j, ¬ @Equation4283 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)

theorem Equation4283_not_termStructuralFromFin_Equation4541 : ¬ Law4283.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4283 j ((@Law4283.models_iff Point (family (bad j))).mp hi))

end Model6

namespace Model74
def table : Fin 12 → Point → Point → Point :=
  ![![![0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2], ![3, 3, 3, 3, 3, 3], ![4, 4, 4, 4, 4, 4], ![5, 5, 5, 5, 5, 5]],
    ![![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5], ![0, 1, 2, 3, 4, 5]],
    ![![4, 4, 4, 4, 4, 4], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3]],
    ![![4, 3, 5, 3, 5, 3], ![2, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![5, 5, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3]],
    ![![4, 2, 3, 3, 5, 3], ![3, 3, 3, 3, 5, 3], ![5, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![5, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3]],
    ![![4, 3, 3, 3, 3, 3], ![4, 3, 3, 3, 3, 3], ![4, 3, 3, 3, 3, 3], ![4, 3, 3, 3, 3, 3], ![4, 3, 3, 3, 3, 3], ![4, 3, 3, 3, 3, 3]],
    ![![5, 5, 5, 5, 5, 5], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3]],
    ![![5, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3]],
    ![![5, 5, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3]],
    ![![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3]],
    ![![5, 3, 3, 3, 3, 3], ![5, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3], ![3, 3, 3, 3, 3, 3]],
    ![![5, 3, 3, 3, 3, 3], ![5, 3, 3, 3, 3, 3], ![5, 3, 3, 3, 3, 3], ![5, 3, 3, 3, 3, 3], ![5, 3, 3, 3, 3, 3], ![5, 3, 3, 3, 3, 3]]]
@[implicit_reducible] def family (i : Fin 12) : Magma Point := ⟨table i⟩
@[implicit_reducible] def source : Magma Point := family 4
def compose : Fin 12 → Fin 12 → Fin 12 :=
  ![![2, 4, 6, 7, 7, 10, 9, 9, 9, 9, 9, 9],
    ![3, 5, 8, 7, 7, 11, 9, 9, 9, 9, 9, 9],
    ![6, 7, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    ![7, 10, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    ![8, 7, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    ![7, 11, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    ![9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    ![9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    ![9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    ![9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    ![9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
    ![9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9]]
theorem closed : source.IsCloneFamily family 0 1 compose where
  fst := by decide
  snd := by decide
  comp := by decide +kernel
theorem source_law : @Equation4541 Point source := by decide
def support : Set Point := {3, 4, 5}
instance : DecidablePred (· ∈ support) := by unfold support; infer_instance
theorem source_outside : ¬ ProjectionOrRange support source.op := by decide
def bad : Fin 2 → Fin 12 := ![3, 4]
theorem coverage : ∀ i, ProjectionOrRange support (family i).op ∨ ∃ j, i = bad j := by decide

private theorem exclude4320 : ∀ j, ¬ @Equation4320 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (5 : Point) ≠ 3) (h 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)

theorem Equation4320_not_termStructuralFromFin_Equation4541 : ¬ Law4320.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4320 j ((@Law4320.models_iff Point (family (bad j))).mp hi))

private theorem exclude4482 : ∀ j, ¬ @Equation4482 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (3 : Point) ≠ 5) (h 1 0)
  · exact (by decide : (5 : Point) ≠ 3) (h 1 0)

theorem Equation4482_not_termStructuralFromFin_Equation4541 : ¬ Law4482.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4482 j ((@Law4482.models_iff Point (family (bad j))).mp hi))

private theorem exclude4544 : ∀ j, ¬ @Equation4544 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (5 : Point) ≠ 3) (h 0 1 0)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1 0)

theorem Equation4544_not_termStructuralFromFin_Equation4541 : ¬ Law4544.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4544 j ((@Law4544.models_iff Point (family (bad j))).mp hi))

private theorem exclude4362 : ∀ j, ¬ @Equation4362 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (5 : Point) ≠ 3) (h 0 1 0)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1 0)

theorem Equation4362_not_termStructuralFromFin_Equation4541 : ¬ Law4362.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4362 j ((@Law4362.models_iff Point (family (bad j))).mp hi))

private theorem exclude4435 : ∀ j, ¬ @Equation4435 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : (5 : Point) ≠ 3) (h 0 1)
  · exact (by decide : (3 : Point) ≠ 5) (h 0 1)

theorem Equation4435_not_termStructuralFromFin_Equation4541 : ¬ Law4435.TermStructuralFromFin Law4541 := by
  apply obstruct source ((@Law4541.models_iff Point source).mpr source_law) family
    closed support source_outside
  intro i hi
  rcases coverage i with hg | ⟨j,rfl⟩
  · exact hg
  · exact False.elim (exclude4435 j ((@Law4435.models_iff Point (family (bad j))).mp hi))

end Model74

end SmallCloneRanges

/-- info: 'SmallCloneRanges.Model27.Equation3529_not_termStructuralFromFin_Equation1037' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model27.Equation3529_not_termStructuralFromFin_Equation1037

/-- info: 'SmallCloneRanges.Model6.Equation4512_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4512_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model6.Equation4290_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4290_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model6.Equation4515_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4515_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model6.Equation4358_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4358_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model6.Equation4364_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4364_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model6.Equation4396_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4396_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model6.Equation4398_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4398_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model6.Equation4369_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4369_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model6.Equation4531_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4531_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model6.Equation4283_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model6.Equation4283_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model74.Equation4320_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model74.Equation4320_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model74.Equation4482_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model74.Equation4482_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model74.Equation4544_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model74.Equation4544_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model74.Equation4362_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model74.Equation4362_not_termStructuralFromFin_Equation4541

/-- info: 'SmallCloneRanges.Model74.Equation4435_not_termStructuralFromFin_Equation4541' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallCloneRanges.Model74.Equation4435_not_termStructuralFromFin_Equation4541
