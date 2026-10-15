import equational_theories.Definability.RecoverySubmagmas
import Mathlib.Tactic.FinCases
open Law Law.MagmaLaw Magma.GenerationOrder RecoverySubmagmas
namespace SmallGeneratedWitnesses

/-- Existing ordinary countermodel from `All4x4Tables/Refutation554.lean`. -/
@[implicit_reducible] def source621 : Magma (Fin 4) := ⟨![![2, 0, 1, 1], ![3, 1, 1, 1], ![3, 2, 2, 2], ![3, 3, 3, 3]]⟩
theorem law621 : @Equation621 (Fin 4) source621 := by decide
theorem generates621 (z : Fin 4) : Generated source621.op {0} z := by
  intro S hs hc
  have h0 : (0 : Fin 4) ∈ S := hs (by simp)
  have h2 : (2 : Fin 4) ∈ S := hc 0 h0 0 h0
  have h1 : (1 : Fin 4) ∈ S := hc 0 h0 2 h2
  have h3 : (3 : Fin 4) ∈ S := hc 2 h2 0 h0
  fin_cases z <;> assumption

theorem Equation3_not_termStructuralFromFin_Equation621_idempotence :
    ¬ Law3.TermStructuralFromFin Law621 :=
  not_idempotent_recovery source621 ((@Law621.models_iff (Fin 4) source621).mpr law621) 0 (by decide)

/-- Existing ordinary countermodel from `All4x4Tables/Refutation846.lean`. -/
@[implicit_reducible] def source626 : Magma (Fin 5) := ⟨![![2, 0, 1, 1, 2], ![3, 3, 4, 4, 1], ![3, 3, 2, 2, 2], ![2, 2, 3, 3, 2], ![4, 3, 0, 0, 3]]⟩
theorem law626 : @Equation626 (Fin 5) source626 := by decide
theorem generates626 (z : Fin 5) : Generated source626.op {0} z := by
  intro S hs hc
  have h0 : (0 : Fin 5) ∈ S := hs (by simp)
  have h2 : (2 : Fin 5) ∈ S := hc 0 h0 0 h0
  have h1 : (1 : Fin 5) ∈ S := hc 0 h0 2 h2
  have h3 : (3 : Fin 5) ∈ S := hc 2 h2 0 h0
  have h4 : (4 : Fin 5) ∈ S := hc 1 h1 2 h2
  fin_cases z <;> assumption

theorem Equation3_not_termStructuralFromFin_Equation626_idempotence :
    ¬ Law3.TermStructuralFromFin Law626 :=
  not_idempotent_recovery source626 ((@Law626.models_iff (Fin 5) source626).mpr law626) 0 (by decide)

/-- Existing ordinary countermodel from `All4x4Tables/Refutation852.lean`. -/
@[implicit_reducible] def source646 : Magma (Fin 6) := ⟨![![1, 2, 0, 0, 1, 0], ![1, 3, 1, 5, 5, 1], ![1, 2, 2, 5, 1, 2], ![5, 3, 3, 0, 0, 3], ![2, 2, 4, 3, 0, 4], ![5, 4, 5, 0, 5, 5]]⟩
theorem law646 : @Equation646 (Fin 6) source646 := by decide
theorem generates646 (z : Fin 6) : Generated source646.op {0} z := by
  intro S hs hc
  have h0 : (0 : Fin 6) ∈ S := hs (by simp)
  have h1 : (1 : Fin 6) ∈ S := hc 0 h0 0 h0
  have h2 : (2 : Fin 6) ∈ S := hc 0 h0 1 h1
  have h3 : (3 : Fin 6) ∈ S := hc 1 h1 1 h1
  have h5 : (5 : Fin 6) ∈ S := hc 1 h1 3 h3
  have h4 : (4 : Fin 6) ∈ S := hc 5 h5 1 h1
  fin_cases z <;> assumption

theorem Equation3_not_termStructuralFromFin_Equation646_idempotence :
    ¬ Law3.TermStructuralFromFin Law646 :=
  not_idempotent_recovery source646 ((@Law646.models_iff (Fin 6) source646).mpr law646) 0 (by decide)

theorem Equation4476_not_termStructuralFromFin_Equation646_generation :
    ¬ Law4476.TermStructuralFromFin Law646 := by
  intro h
  obtain ⟨N,hN,_,hr⟩ := h source646 ((@Law646.models_iff (Fin 6) source646).mpr law646)
  have hn := card_le_three_of_recovery generates646 hr
    (CollapsedUnaryProducts.table4476 N ((@Law4476.models_iff (Fin 6) N).mp hN) 0)
  norm_num at hn

end SmallGeneratedWitnesses

/-- info: 'SmallGeneratedWitnesses.Equation3_not_termStructuralFromFin_Equation621_idempotence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallGeneratedWitnesses.Equation3_not_termStructuralFromFin_Equation621_idempotence

/-- info: 'SmallGeneratedWitnesses.Equation3_not_termStructuralFromFin_Equation626_idempotence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallGeneratedWitnesses.Equation3_not_termStructuralFromFin_Equation626_idempotence

/-- info: 'SmallGeneratedWitnesses.Equation3_not_termStructuralFromFin_Equation646_idempotence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallGeneratedWitnesses.Equation3_not_termStructuralFromFin_Equation646_idempotence

/-- info: 'SmallGeneratedWitnesses.Equation4476_not_termStructuralFromFin_Equation646_generation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallGeneratedWitnesses.Equation4476_not_termStructuralFromFin_Equation646_generation
