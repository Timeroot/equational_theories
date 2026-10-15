import equational_theories.Definability.FourPointTable

/-! Generated finite endomorphism obstruction. Small source lists are checked
in the kernel; bv_decide verifies that the target lists are exhaustive. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FourPointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma.UnaryTail1002

def step (x : Point) : Point := if x = 0 then 1 else if x = 1 then 0 else if x = 2 then 0 else 2

def endoTest (c : Code) : Prop :=
  decode c (step 0) (step 0) = step (decode c 0 0) ∧
  decode c (step 0) (step 1) = step (decode c 0 1) ∧
  decode c (step 0) (step 2) = step (decode c 0 2) ∧
  decode c (step 0) (step 3) = step (decode c 0 3) ∧
  decode c (step 1) (step 0) = step (decode c 1 0) ∧
  decode c (step 1) (step 1) = step (decode c 1 1) ∧
  decode c (step 1) (step 2) = step (decode c 1 2) ∧
  decode c (step 1) (step 3) = step (decode c 1 3) ∧
  decode c (step 2) (step 0) = step (decode c 2 0) ∧
  decode c (step 2) (step 1) = step (decode c 2 1) ∧
  decode c (step 2) (step 2) = step (decode c 2 2) ∧
  decode c (step 2) (step 3) = step (decode c 2 3) ∧
  decode c (step 3) (step 0) = step (decode c 3 0) ∧
  decode c (step 3) (step 1) = step (decode c 3 1) ∧
  decode c (step 3) (step 2) = step (decode c 3 2) ∧
  decode c (step 3) (step 3) = step (decode c 3 3)

theorem endoTest_encode (f : Point → Point → Point) (h : Commutes step f) :
    endoTest (encode f) := by
  unfold endoTest
  simp only [decode_encode]
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 1 0, h 1 1, h 1 2, h 1 3, h 2 0, h 2 1, h 2 2, h 2 3, h 3 0, h 3 1, h 3 2, h 3 3⟩

def codes844 : Fin 5 → Code := ![1062884608, 1067078912, 1062900992, 1067095296, 4289352960]

def codes1042 : Fin 5 → Code := ![1062884608, 1067078912, 1062900992, 1067095296, 4289352960]

def codes1250 : Fin 3 → Code := ![1062884608, 1067078912, 4289352960]

theorem source844_injective : Function.Injective (fun i => decode (codes844 i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes844 := by decide +kernel
  exact hi hc

theorem source844_law : ∀ i, @Equation844 Point ⟨decode (codes844 i)⟩ := by
  decide +kernel

theorem source844_endo : ∀ i, Commutes step (decode (codes844 i)) := by
  decide +kernel

theorem source1042_injective : Function.Injective (fun i => decode (codes1042 i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes1042 := by decide +kernel
  exact hi hc

theorem source1042_law : ∀ i, @Equation1042 Point ⟨decode (codes1042 i)⟩ := by
  decide +kernel

theorem source1042_endo : ∀ i, Commutes step (decode (codes1042 i)) := by
  decide +kernel

def test1250 (c : Code) : Prop :=
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 0) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 0) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 0) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 0) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 0) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 0) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 0) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 0) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 0) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 1) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 1) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 1) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 1) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 1) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 1) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 1) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 1) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 1) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 2) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 2) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 2) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 2) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 2) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 2) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 2) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 2) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 2) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 3) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 3) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 3) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 3) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 3) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 3) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 3) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 3) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 3) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 3))

theorem test1250_encode (f : Point → Point → Point) (h : @Equation1250 Point ⟨f⟩) :
    test1250 (encode f) := by
  unfold test1250
  simp only [decode_encode]
  exact ⟨h 0 0 0, h 0 0 1, h 0 0 2, h 0 0 3, h 0 1 0, h 0 1 1, h 0 1 2, h 0 1 3, h 0 2 0, h 0 2 1, h 0 2 2, h 0 2 3, h 0 3 0, h 0 3 1, h 0 3 2, h 0 3 3, h 1 0 0, h 1 0 1, h 1 0 2, h 1 0 3, h 1 1 0, h 1 1 1, h 1 1 2, h 1 1 3, h 1 2 0, h 1 2 1, h 1 2 2, h 1 2 3, h 1 3 0, h 1 3 1, h 1 3 2, h 1 3 3, h 2 0 0, h 2 0 1, h 2 0 2, h 2 0 3, h 2 1 0, h 2 1 1, h 2 1 2, h 2 1 3, h 2 2 0, h 2 2 1, h 2 2 2, h 2 2 3, h 2 3 0, h 2 3 1, h 2 3 2, h 2 3 3, h 3 0 0, h 3 0 1, h 3 0 2, h 3 0 3, h 3 1 0, h 3 1 1, h 3 1 2, h 3 1 3, h 3 2 0, h 3 2 1, h 3 2 2, h 3 2 3, h 3 3 0, h 3 3 1, h 3 3 2, h 3 3 3⟩

theorem cover1250_bits (c : Code) (he : endoTest c) (h : test1250 c) :
    ∃ i, codes1250 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes1250, Fin.cons_zero,
    Fin.cons_succ]
  change 1062884608 = c ∨ 1067078912 = c ∨ 4289352960 = c ∨ False
  unfold endoTest test1250 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover1250 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1250 Point ⟨f⟩) : ∃ i, decode (codes1250 i) = f := by
  obtain ⟨i, hi⟩ := cover1250_bits (encode f) (endoTest_encode f he) (test1250_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

end Magma.UnaryTail1002

open Magma.UnaryTail1002

theorem Equation1250_not_termStructuralFromFin_Equation844_unaryTail : ¬ Law1250.TermStructuralFromFin Law844 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes844 i))
    (fun i => decode (codes1250 i)) source844_injective
  · intro i
    exact (@Law844.models_iff Point ⟨decode (codes844 i)⟩).mpr (source844_law i)
  · exact source844_endo
  · intro f he h
    exact cover1250 f he ((@Law1250.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1250_not_termStructuralFromFin_Equation844_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1250_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1250_not_termStructuralFromFin_Equation844_unaryTail

theorem Equation1250_not_termStructuralFromFin_Equation1042_unaryTail : ¬ Law1250.TermStructuralFromFin Law1042 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1042 i))
    (fun i => decode (codes1250 i)) source1042_injective
  · intro i
    exact (@Law1042.models_iff Point ⟨decode (codes1042 i)⟩).mpr (source1042_law i)
  · exact source1042_endo
  · intro f he h
    exact cover1250 f he ((@Law1250.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1250_not_termStructuralFromFin_Equation1042_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1250_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1250_not_termStructuralFromFin_Equation1042_unaryTail

