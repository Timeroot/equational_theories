import equational_theories.Definability.FourPointTable

/-! Generated finite endomorphism obstruction. Small source lists are checked
in the kernel; bv_decide verifies that the target lists are exhaustive. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FourPointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma.UnaryTail0211

def step (x : Point) : Point := if x = 0 then 0 else if x = 1 then 2 else if x = 2 then 1 else 1

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

def codes1050 : Fin 2 → Code := ![4289352960, 1397885184]

def codes1435 : Fin 1 → Code := ![4289352960]

def codes1638 : Fin 1 → Code := ![4289352960]

theorem source1050_injective : Function.Injective (fun i => decode (codes1050 i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes1050 := by decide +kernel
  exact hi hc

theorem source1050_law : ∀ i, @Equation1050 Point ⟨decode (codes1050 i)⟩ := by
  decide +kernel

theorem source1050_endo : ∀ i, Commutes step (decode (codes1050 i)) := by
  decide +kernel

def test1435 (c : Code) : Prop :=
  0 = (decode c (decode c 0 0) (decode c 0 (decode c 0 0))) ∧
  0 = (decode c (decode c 0 0) (decode c 1 (decode c 1 1))) ∧
  0 = (decode c (decode c 0 0) (decode c 2 (decode c 2 2))) ∧
  0 = (decode c (decode c 0 0) (decode c 3 (decode c 3 3))) ∧
  1 = (decode c (decode c 1 1) (decode c 0 (decode c 0 0))) ∧
  1 = (decode c (decode c 1 1) (decode c 1 (decode c 1 1))) ∧
  1 = (decode c (decode c 1 1) (decode c 2 (decode c 2 2))) ∧
  1 = (decode c (decode c 1 1) (decode c 3 (decode c 3 3))) ∧
  2 = (decode c (decode c 2 2) (decode c 0 (decode c 0 0))) ∧
  2 = (decode c (decode c 2 2) (decode c 1 (decode c 1 1))) ∧
  2 = (decode c (decode c 2 2) (decode c 2 (decode c 2 2))) ∧
  2 = (decode c (decode c 2 2) (decode c 3 (decode c 3 3))) ∧
  3 = (decode c (decode c 3 3) (decode c 0 (decode c 0 0))) ∧
  3 = (decode c (decode c 3 3) (decode c 1 (decode c 1 1))) ∧
  3 = (decode c (decode c 3 3) (decode c 2 (decode c 2 2))) ∧
  3 = (decode c (decode c 3 3) (decode c 3 (decode c 3 3)))

theorem test1435_encode (f : Point → Point → Point) (h : @Equation1435 Point ⟨f⟩) :
    test1435 (encode f) := by
  unfold test1435
  simp only [decode_encode]
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 1 0, h 1 1, h 1 2, h 1 3, h 2 0, h 2 1, h 2 2, h 2 3, h 3 0, h 3 1, h 3 2, h 3 3⟩

theorem cover1435_bits (c : Code) (he : endoTest c) (h : test1435 c) :
    ∃ i, codes1435 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes1435, Fin.cons_zero,
    Fin.cons_succ]
  change 4289352960 = c ∨ False
  unfold endoTest test1435 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover1435 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1435 Point ⟨f⟩) : ∃ i, decode (codes1435 i) = f := by
  obtain ⟨i, hi⟩ := cover1435_bits (encode f) (endoTest_encode f he) (test1435_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test1638 (c : Code) : Prop :=
  0 = (decode c (decode c 0 0) (decode c (decode c 0 0) 0)) ∧
  0 = (decode c (decode c 0 0) (decode c (decode c 1 1) 1)) ∧
  0 = (decode c (decode c 0 0) (decode c (decode c 2 2) 2)) ∧
  0 = (decode c (decode c 0 0) (decode c (decode c 3 3) 3)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 0 0) 0)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 1 1) 1)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 2 2) 2)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 3 3) 3)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 0 0) 0)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 1 1) 1)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 2 2) 2)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 3 3) 3)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 0 0) 0)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 1 1) 1)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 2 2) 2)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 3 3) 3))

theorem test1638_encode (f : Point → Point → Point) (h : @Equation1638 Point ⟨f⟩) :
    test1638 (encode f) := by
  unfold test1638
  simp only [decode_encode]
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 1 0, h 1 1, h 1 2, h 1 3, h 2 0, h 2 1, h 2 2, h 2 3, h 3 0, h 3 1, h 3 2, h 3 3⟩

theorem cover1638_bits (c : Code) (he : endoTest c) (h : test1638 c) :
    ∃ i, codes1638 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes1638, Fin.cons_zero,
    Fin.cons_succ]
  change 4289352960 = c ∨ False
  unfold endoTest test1638 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover1638 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1638 Point ⟨f⟩) : ∃ i, decode (codes1638 i) = f := by
  obtain ⟨i, hi⟩ := cover1638_bits (encode f) (endoTest_encode f he) (test1638_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

end Magma.UnaryTail0211

open Magma.UnaryTail0211

theorem Equation1435_not_termStructuralFromFin_Equation1050_unaryTail : ¬ Law1435.TermStructuralFromFin Law1050 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1050 i))
    (fun i => decode (codes1435 i)) source1050_injective
  · intro i
    exact (@Law1050.models_iff Point ⟨decode (codes1050 i)⟩).mpr (source1050_law i)
  · exact source1050_endo
  · intro f he h
    exact cover1435 f he ((@Law1435.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1435_not_termStructuralFromFin_Equation1050_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1435_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1435_not_termStructuralFromFin_Equation1050_unaryTail

theorem Equation1638_not_termStructuralFromFin_Equation1050_unaryTail : ¬ Law1638.TermStructuralFromFin Law1050 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1050 i))
    (fun i => decode (codes1638 i)) source1050_injective
  · intro i
    exact (@Law1050.models_iff Point ⟨decode (codes1050 i)⟩).mpr (source1050_law i)
  · exact source1050_endo
  · intro f he h
    exact cover1638 f he ((@Law1638.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1638_not_termStructuralFromFin_Equation1050_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1638_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1638_not_termStructuralFromFin_Equation1050_unaryTail

