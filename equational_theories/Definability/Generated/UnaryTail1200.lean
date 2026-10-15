import equational_theories.Definability.FourPointTable

/-! Generated finite endomorphism obstruction. Small source lists are checked
in the kernel; bv_decide verifies that the target lists are exhaustive. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FourPointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma.UnaryTail1200

def step (x : Point) : Point := if x = 0 then 1 else if x = 1 then 2 else if x = 2 then 0 else 0

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

def codes1029 : Fin 11 → Code := ![4205466880, 4272575744, 4222244096, 4289352960, 4087502416, 4255712520, 4053861976, 117856417, 117856481, 1549312262, 1549328646]

def codes1632 : Fin 8 → Code := ![4205466880, 4272575744, 4222244096, 4289352960, 3219805440, 4087502416, 4255712520, 4053861976]

theorem source1029_injective : Function.Injective (fun i => decode (codes1029 i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes1029 := by decide +kernel
  exact hi hc

theorem source1029_law : ∀ i, @Equation1029 Point ⟨decode (codes1029 i)⟩ := by
  decide +kernel

theorem source1029_endo : ∀ i, Commutes step (decode (codes1029 i)) := by
  decide +kernel

def test1632 (c : Code) : Prop :=
  0 = (decode c (decode c 0 0) (decode c (decode c 0 0) 0)) ∧
  0 = (decode c (decode c 0 0) (decode c (decode c 0 1) 1)) ∧
  0 = (decode c (decode c 0 0) (decode c (decode c 0 2) 2)) ∧
  0 = (decode c (decode c 0 0) (decode c (decode c 0 3) 3)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 1 0) 0)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 1 1) 1)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 1 2) 2)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 1 3) 3)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 2 0) 0)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 2 1) 1)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 2 2) 2)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 2 3) 3)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 3 0) 0)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 3 1) 1)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 3 2) 2)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 3 3) 3))

theorem test1632_encode (f : Point → Point → Point) (h : @Equation1632 Point ⟨f⟩) :
    test1632 (encode f) := by
  unfold test1632
  simp only [decode_encode]
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 1 0, h 1 1, h 1 2, h 1 3, h 2 0, h 2 1, h 2 2, h 2 3, h 3 0, h 3 1, h 3 2, h 3 3⟩

theorem cover1632_bits (c : Code) (he : endoTest c) (h : test1632 c) :
    ∃ i, codes1632 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes1632, Fin.cons_zero,
    Fin.cons_succ]
  change 4205466880 = c ∨ 4272575744 = c ∨ 4222244096 = c ∨ 4289352960 = c ∨ 3219805440 = c ∨ 4087502416 = c ∨ 4255712520 = c ∨ 4053861976 = c ∨ False
  unfold endoTest test1632 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover1632 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1632 Point ⟨f⟩) : ∃ i, decode (codes1632 i) = f := by
  obtain ⟨i, hi⟩ := cover1632_bits (encode f) (endoTest_encode f he) (test1632_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

end Magma.UnaryTail1200

open Magma.UnaryTail1200

theorem Equation1632_not_termStructuralFromFin_Equation1029_unaryTail : ¬ Law1632.TermStructuralFromFin Law1029 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1029 i))
    (fun i => decode (codes1632 i)) source1029_injective
  · intro i
    exact (@Law1029.models_iff Point ⟨decode (codes1029 i)⟩).mpr (source1029_law i)
  · exact source1029_endo
  · intro f he h
    exact cover1632 f he ((@Law1632.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1632_not_termStructuralFromFin_Equation1029_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1632_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1632_not_termStructuralFromFin_Equation1029_unaryTail

