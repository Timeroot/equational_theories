import equational_theories.Definability.Generated.FullAut690To3321
import equational_theories.Definability.Generated.FullAut690To3323
import equational_theories.Definability.Generated.FullAut690To3520

/-! Reuse complete orbit-family exclusions with an independently checked source. -/
open Law Law.MagmaLaw Magma.FiniteSymmetry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ReuseAut1446
def sourceData : Array (Array (Fin 12)) := #[#[7, 8, 7, 7, 8, 8, 8, 8, 8, 7, 8, 8], #[8, 8, 6, 6, 8, 6, 6, 6, 6, 6, 8, 6], #[7, 6, 6, 7, 7, 6, 7, 7, 7, 7, 7, 6], #[10, 11, 11, 10, 11, 10, 10, 11, 11, 11, 11, 11], #[9, 11, 9, 11, 11, 9, 9, 11, 9, 9, 9, 9], #[10, 10, 9, 10, 9, 9, 10, 10, 9, 10, 10, 10], #[2, 2, 2, 1, 2, 2, 1, 2, 1, 1, 2, 2], #[0, 0, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0], #[1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0], #[4, 5, 5, 5, 5, 5, 4, 5, 5, 4, 5, 4], #[3, 5, 3, 3, 3, 3, 3, 5, 3, 5, 5, 3], #[4, 4, 3, 4, 4, 4, 4, 4, 3, 4, 3, 3]]
@[implicit_reducible] def source : Magma (Fin 12) :=
  ⟨fun x y => (sourceData.getD x.val #[]).getD y.val 0⟩
end Magma.ReuseAut1446

theorem Equation3321_not_structuralFromFin_Equation1446_reuseAut1446 : ¬ Law3321.StructuralFromFin Law1446 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin Magma.ReuseAut1446.source
    Magma.FullAut690To3321.genPerm Magma.FullAut690To3321.probePerm Magma.FullAut690To3321.pattern Magma.FullAut690To3321.fam Magma.FullAut690To3321.coverage
  · exact (@Law1446.models_iff (Fin 12) Magma.ReuseAut1446.source).mpr (by native_decide)
  · native_decide
  · native_decide
  · intro p hp
    exact Magma.FullAut690To3321.target3321 p ((@Law3321.models_iff (Fin 12) (Magma.FullAut690To3321.fam p)).mp hp)

/-- info: 'Equation3321_not_structuralFromFin_Equation1446_reuseAut1446' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3321_not_structuralFromFin_Equation1446_reuseAut1446._native.native_decide.ax_1_1,
 Equation3321_not_structuralFromFin_Equation1446_reuseAut1446._native.native_decide.ax_1_2,
 Equation3321_not_structuralFromFin_Equation1446_reuseAut1446._native.native_decide.ax_1_3,
 Magma.FullAut690To3321.gen_inverse._native.native_decide.ax_1_1,
 Magma.FullAut690To3321.probe_inverse._native.native_decide.ax_1_1,
 Magma.FullAut690To3321.stabilizers_correct._native.native_decide.ax_1_1,
 Magma.FullAut690To3321.transport_correct._native.native_decide.ax_1_1,
 Magma.FullAut690To3321.values_complete._native.native_decide.ax_1_1,
 Magma.FullAut690To3321.native_cell_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3321.native_checked3321._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3321.native_orbit_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3321.native_places_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3321.native_probe_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3321.native_sizes_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3321.places_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3321.sizes_pos._native.native_decide.ax_1_1✝] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3321_not_structuralFromFin_Equation1446_reuseAut1446

theorem Equation3323_not_structuralFromFin_Equation1446_reuseAut1446 : ¬ Law3323.StructuralFromFin Law1446 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin Magma.ReuseAut1446.source
    Magma.FullAut690To3323.genPerm Magma.FullAut690To3323.probePerm Magma.FullAut690To3323.pattern Magma.FullAut690To3323.fam Magma.FullAut690To3323.coverage
  · exact (@Law1446.models_iff (Fin 12) Magma.ReuseAut1446.source).mpr (by native_decide)
  · native_decide
  · native_decide
  · intro p hp
    exact Magma.FullAut690To3323.target3323 p ((@Law3323.models_iff (Fin 12) (Magma.FullAut690To3323.fam p)).mp hp)

/-- info: 'Equation3323_not_structuralFromFin_Equation1446_reuseAut1446' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3323_not_structuralFromFin_Equation1446_reuseAut1446._native.native_decide.ax_1_1,
 Equation3323_not_structuralFromFin_Equation1446_reuseAut1446._native.native_decide.ax_1_2,
 Equation3323_not_structuralFromFin_Equation1446_reuseAut1446._native.native_decide.ax_1_3,
 Magma.FullAut690To3323.gen_inverse._native.native_decide.ax_1_1,
 Magma.FullAut690To3323.probe_inverse._native.native_decide.ax_1_1,
 Magma.FullAut690To3323.stabilizers_correct._native.native_decide.ax_1_1,
 Magma.FullAut690To3323.transport_correct._native.native_decide.ax_1_1,
 Magma.FullAut690To3323.values_complete._native.native_decide.ax_1_1,
 Magma.FullAut690To3323.native_cell_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3323.native_checked3323._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3323.native_orbit_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3323.native_places_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3323.native_probe_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3323.native_sizes_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3323.places_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3323.sizes_pos._native.native_decide.ax_1_1✝] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3323_not_structuralFromFin_Equation1446_reuseAut1446

theorem Equation3520_not_structuralFromFin_Equation1446_reuseAut1446 : ¬ Law3520.StructuralFromFin Law1446 := by
  apply Magma.FiniteSymmetry.not_structuralFromFin Magma.ReuseAut1446.source
    Magma.FullAut690To3520.genPerm Magma.FullAut690To3520.probePerm Magma.FullAut690To3520.pattern Magma.FullAut690To3520.fam Magma.FullAut690To3520.coverage
  · exact (@Law1446.models_iff (Fin 12) Magma.ReuseAut1446.source).mpr (by native_decide)
  · native_decide
  · native_decide
  · intro p hp
    exact Magma.FullAut690To3520.target3520 p ((@Law3520.models_iff (Fin 12) (Magma.FullAut690To3520.fam p)).mp hp)

/-- info: 'Equation3520_not_structuralFromFin_Equation1446_reuseAut1446' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Equation3520_not_structuralFromFin_Equation1446_reuseAut1446._native.native_decide.ax_1_1,
 Equation3520_not_structuralFromFin_Equation1446_reuseAut1446._native.native_decide.ax_1_2,
 Equation3520_not_structuralFromFin_Equation1446_reuseAut1446._native.native_decide.ax_1_3,
 Magma.FullAut690To3520.gen_inverse._native.native_decide.ax_1_1,
 Magma.FullAut690To3520.probe_inverse._native.native_decide.ax_1_1,
 Magma.FullAut690To3520.stabilizers_correct._native.native_decide.ax_1_1,
 Magma.FullAut690To3520.transport_correct._native.native_decide.ax_1_1,
 Magma.FullAut690To3520.values_complete._native.native_decide.ax_1_1,
 Magma.FullAut690To3520.native_cell_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3520.native_checked3520._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3520.native_orbit_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3520.native_places_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3520.native_probe_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3520.native_sizes_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3520.places_correct._native.native_decide.ax_1_1✝,
 Magma.FullAut690To3520.sizes_pos._native.native_decide.ax_1_1✝] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3520_not_structuralFromFin_Equation1446_reuseAut1446

