import equational_theories.Asterix
import equational_theories.Confluence1
import equational_theories.Confluence2
import equational_theories.Equations.All
import equational_theories.Generated.Greedy.Eq1112
import equational_theories.Generated.Greedy.Eq476
import equational_theories.ManuallyProved.Equation1076
import equational_theories.ManuallyProved.Equation713
import equational_theories.Parastrophes.Attributes
import equational_theories.Superposition

/-! The existing infinite countermodels refute cancellation hypotheses.
These are the finite-implication arguments with their permutation step replaced
by explicit injectivity; no finiteness or new model search is used. -/
namespace Parastrophes.Catalogue

private theorem cancellation65_1426 {G : Type} [Magma G]
    (h : Equation65 G) (hQ : IsSideQuasigroup .left (inferInstance : Magma G)) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ X))) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ s)) := (hQ Y).1.comp (Function.injective_id)
    apply hi
    simp only [← h]
  have step14 : sK0 ≠ sK0 := superpose step10 step9
  subsumption step14 rfl

/-- The saved E65 countermodel refutes E1426, which would follow from
left cancellation. -/
@[parastrophe_result] theorem not_leftQuasigroup65_all_rotation :
    ¬ SideQuasigroupLaw .all Law65 .left := by
  intro h
  obtain ⟨G, M, hE, _, _, hn, _, _⟩ := Asterix.Equation65_facts
  have hQ := h G M trivial ((@Law65.models_iff G M).mpr hE)
  exact hn (@cancellation65_1426 G M hE hQ)

private theorem cancellation476_3862 {G : Type} [Magma G]
    (h : Equation476 G) (hQ : IsSideQuasigroup .left (inferInstance : Magma G)) : Equation3862 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := mod_symm (h ..)
  have step9 : (sK0 ◇ sK0) ≠ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ X) ◇ (Y ◇ (Y ◇ (Y ◇ X)))) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ s)) := (hQ Y).1.comp (Function.injective_id)
    apply hi
    simp only [← h]
  have step15 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose step8 step10
  have step17 : (sK0 ◇ sK0) ≠ (sK0 ◇ sK0) := superpose step15 step9
  subsumption step17 rfl

/-- The saved E476 countermodel refutes E3862, which would follow from
left cancellation. -/
@[parastrophe_result] theorem not_leftQuasigroup476_all_rotation :
    ¬ SideQuasigroupLaw .all Law476 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Equation476_not_implies_Equation3862
  have hQ := h G M trivial ((@Law476.models_iff G M).mpr hE)
  exact hn (@cancellation476_3862 G M hE hQ)

private theorem cancellation504_1925 {G : Type} [Magma G]
    (h : Equation504 G) (hQ : IsSideQuasigroup .left (inferInstance : Magma G)) : Equation1925 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step10 : sK0 ≠ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ X)) ◇ (Y ◇ Y)) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ (Y ◇ s))) := (hQ Y).1.comp ((hQ Y).1.comp (Function.injective_id))
    apply hi
    simp only [← h]
  have step15 : sK0 ≠ sK0 := superpose step11 step10
  subsumption step15 rfl

/-- The saved E504 countermodel refutes E1925, which would follow from
left cancellation. -/
@[parastrophe_result] theorem not_leftQuasigroup504_all_rotation :
    ¬ SideQuasigroupLaw .all Law504 .left := by
  intro h
  obtain ⟨G, M, hE, _, _, _, hn⟩ := rw504.Facts
  have hQ := h G M trivial ((@Law504.models_iff G M).mpr hE)
  exact hn (@cancellation504_1925 G M hE hQ)

private theorem cancellation713_1426 {G : Type} [Magma G]
    (h : Equation713 G) (hQ : IsSideQuasigroup .left (inferInstance : Magma G)) : Equation1426 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (Y ◇ (Y ◇ X))) ◇ (Y ◇ (Y ◇ X))) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ (Y ◇ s))) := (hQ Y).1.comp ((hQ Y).1.comp (Function.injective_id))
    apply hi
    simp only [← h]
  have step12 (X Y : G) : (Y ◇ ((Y ◇ (Y ◇ X)) ◇ (Y ◇ X))) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ s)) := (hQ Y).1.comp (Function.injective_id)
    apply hi
    simp only [← h]
  have step14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose step9 step12
  have step15 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose step12 step12
  have step21 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose step11 step9
  have step26 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose step9 step14
  have step39 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := superpose step11 step15
  have step54 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0)) := superpose step39 step21
  have step64 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step26 step9
  have step67 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose step26 step64
  have step75 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0)) := superpose step26 step54
  have step90 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step67 step75
  have step91 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose step26 step90
  have step93 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose step91 step67
  have step158 : sK0 ≠ sK0 := superpose step93 step10
  subsumption step158 rfl

/-- The saved E713 countermodel refutes E1426, which would follow from
left cancellation. -/
@[parastrophe_result] theorem not_leftQuasigroup713_all_rotation :
    ¬ SideQuasigroupLaw .all Law713 .left := by
  intro h
  obtain ⟨G, M, hE, _, hn, _, _⟩ := Eq713.not_817_1426_3862_4065
  have hQ := h G M trivial ((@Law713.models_iff G M).mpr hE)
  exact hn (@cancellation713_1426 G M hE hQ)

private theorem cancellation1112_8 {G : Type} [Magma G]
    (h : Equation1112 G) (hQ : IsSideQuasigroup .left (inferInstance : Magma G)) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := mod_symm (h ..)
  have step9 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step10 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ (Y ◇ X)) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ s)) := (hQ Y).1.comp (Function.injective_id)
    apply hi
    simp only [← h]
  have step13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose step8 step10
  have step16 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose step13 step10
  have step18 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose step10 step16
  have step20 : sK0 ≠ sK0 := superpose step18 step9
  subsumption step20 rfl

/-- The saved E1112 countermodel refutes E8, which would follow from
left cancellation. -/
@[parastrophe_result] theorem not_leftQuasigroup1112_all_rotation :
    ¬ SideQuasigroupLaw .all Law1112 .left := by
  intro h
  obtain ⟨G, M, hE, hn⟩ := Equation1112_not_implies_Equation8
  have hQ := h G M trivial ((@Law1112.models_iff G M).mpr hE)
  exact hn (@cancellation1112_8 G M hE hQ)

private theorem cancellation1076_3 {G : Type} [Magma G]
    (h : Equation1076 G) (hQ : IsQuasigroup (inferInstance : Magma G)) : Equation3 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : sK0 ≠ (sK0 ◇ sK0) := mod_symm nh
  have step11 (X Y : G) : ((Y ◇ (X ◇ Y)) ◇ ((Y ◇ (X ◇ Y)) ◇ Y)) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ (s ◇ Y))) := (hQ.1 Y).1.comp ((hQ.2 Y).1.comp (Function.injective_id))
    apply hi
    simp only [← h]
  have step12 (X Y : G) : (((Y ◇ X) ◇ ((Y ◇ X) ◇ Y)) ◇ Y) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ s)) := (hQ.1 Y).1.comp (Function.injective_id)
    apply hi
    simp only [← h]
  have step13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) = X1 := superpose step9 step9
  have step15 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ X1)) := superpose step12 step9
  have step75 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose step12 step15
  have step91 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose step75 step12
  have step92 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose step75 step13
  have step102 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose step11 step92
  have step103 (X0 : G) : (X0 ◇ X0) = X0 := superpose step91 step102
  have step175 : sK0 ≠ sK0 := superpose step103 step10
  subsumption step175 rfl

/-- The saved E1076 countermodel refutes E3, which would follow from
two-sided cancellation. -/
@[parastrophe_result] theorem not_quasigroup1076_all_rotation :
    ¬ QuasigroupLaw .all Law1076 := by
  intro h
  obtain ⟨G, M, hE, hn, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := Eq1076.refute_seed1
  have hQ := h G M trivial ((@Law1076.models_iff G M).mpr hE)
  exact hn (@cancellation1076_3 G M hE hQ)

private theorem cancellation1110_8 {G : Type} [Magma G]
    (h : Equation1110 G) (hQ : IsQuasigroup (inferInstance : Magma G)) : Equation8 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, nh⟩ := nh
  have step11 : sK0 ≠ (sK0 ◇ (sK0 ◇ sK0)) := mod_symm nh
  have step12 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ Y)) ◇ (Y ◇ ((Y ◇ X) ◇ Y))) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ ((Y ◇ s) ◇ Y))) := (hQ.1 Y).1.comp ((hQ.2 Y).1.comp ((hQ.1 Y).1.comp (Function.injective_id)))
    apply hi
    simp only [← h]
  have step14 (X Y : G) : ((Y ◇ ((Y ◇ X) ◇ (Y ◇ X))) ◇ Y) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ s)) := (hQ.1 Y).1.comp (Function.injective_id)
    apply hi
    simp only [← h]
  have step15 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose step14 step14
  have step74 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose step14 step15
  have step160 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := superpose step74 step12
  have step167 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose step12 step160
  have step201 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose step167 step14
  have step244 : sK0 ≠ sK0 := superpose step201 step11
  subsumption step244 rfl

/-- The saved E1110 countermodel refutes E8, which would follow from
two-sided cancellation. -/
@[parastrophe_result] theorem not_quasigroup1110_all_rotation :
    ¬ QuasigroupLaw .all Law1110 := by
  intro h
  obtain ⟨G, M, hE, hn, _, _, _, _, _, _, _⟩ := rw1110.Facts
  have hQ := h G M trivial ((@Law1110.models_iff G M).mpr hE)
  exact hn (@cancellation1110_8 G M hE hQ)

private theorem cancellation1276_4273 {G : Type} [Magma G]
    (h : Equation1276 G) (hQ : IsQuasigroup (inferInstance : Magma G)) : Equation4273 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have step9 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have step10 : (sK0 ◇ (sK0 ◇ sK0)) ≠ (sK1 ◇ (sK0 ◇ sK1)) := mod_symm nh
  have step11 (X Y : G) : (((Y ◇ (X ◇ Y)) ◇ (Y ◇ (X ◇ Y))) ◇ (Y ◇ (X ◇ Y))) = X := by
    have hi : Function.Injective (fun s : G => (Y ◇ (s ◇ Y))) := (hQ.1 Y).1.comp ((hQ.2 Y).1.comp (Function.injective_id))
    apply hi
    simp only [← h]
  have step17 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X2)) := superpose step11 step9
  have step40 (X0 : G) : (sK0 ◇ (sK0 ◇ sK0)) ≠ (X0 ◇ (sK0 ◇ X0)) := superpose step17 step10
  subsumption step40 step17

/-- The saved E1276 countermodel refutes E4273, which would follow from
two-sided cancellation. -/
@[parastrophe_result] theorem not_quasigroup1276_all_rotation :
    ¬ QuasigroupLaw .all Law1276 := by
  intro h
  obtain ⟨G, M, hE, hn, _⟩ := rw1276.Facts
  have hQ := h G M trivial ((@Law1276.models_iff G M).mpr hE)
  exact hn (@cancellation1276_4273 G M hE hQ)

end Parastrophes.Catalogue
