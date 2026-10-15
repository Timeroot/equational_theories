import equational_theories.Definability.FourPointTable

/-! Generated finite endomorphism obstruction. Small source lists are checked
in the kernel; bv_decide verifies that the target lists are exhaustive. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FourPointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma.UnaryTail0032

def step (x : Point) : Point := if x = 0 then 0 else if x = 1 then 0 else if x = 2 then 3 else 2

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

def codes1249 : Fin 30 → Code := ![252313856, 252330240, 252317952, 252334336, 252314880, 252331264, 252318976, 252335360, 1066008832, 1066025216, 1066012928, 1066029312, 1066009856, 1066026240, 1066013952, 1066030336, 801767680, 801784064, 801771776, 801788160, 801768704, 801785088, 801772800, 801789184, 3475656960, 3475657984, 4289351936, 4289352960, 3392123312, 3392124336]

def codes1263 : Fin 34 → Code := ![252313856, 252330240, 252317952, 252334336, 252314880, 252331264, 252318976, 252335360, 1066008832, 1066025216, 1066012928, 1066029312, 1066009856, 1066026240, 1066013952, 1066030336, 801767680, 801784064, 801771776, 801788160, 801768704, 801785088, 801772800, 801789184, 4289351936, 4289352960, 2402943232, 2402959616, 2402947328, 2402963712, 2402944256, 2402960640, 2402948352, 2402964736]

theorem source1263_injective : Function.Injective (fun i => decode (codes1263 i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes1263 := by decide +kernel
  exact hi hc

theorem source1263_law : ∀ i, @Equation1263 Point ⟨decode (codes1263 i)⟩ := by
  decide +kernel

theorem source1263_endo : ∀ i, Commutes step (decode (codes1263 i)) := by
  decide +kernel

def test1249 (c : Code) : Prop :=
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 0) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 0) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 0) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 1) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 1) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 1) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 2) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 2) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 2) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 3) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 3) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 3) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 3))

theorem test1249_encode (f : Point → Point → Point) (h : @Equation1249 Point ⟨f⟩) :
    test1249 (encode f) := by
  unfold test1249
  simp only [decode_encode]
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 1 0, h 1 1, h 1 2, h 1 3, h 2 0, h 2 1, h 2 2, h 2 3, h 3 0, h 3 1, h 3 2, h 3 3⟩

theorem cover1249_bits (c : Code) (he : endoTest c) (h : test1249 c) :
    ∃ i, codes1249 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes1249, Fin.cons_zero,
    Fin.cons_succ]
  change 252313856 = c ∨ 252330240 = c ∨ 252317952 = c ∨ 252334336 = c ∨ 252314880 = c ∨ 252331264 = c ∨ 252318976 = c ∨ 252335360 = c ∨ 1066008832 = c ∨ 1066025216 = c ∨ 1066012928 = c ∨ 1066029312 = c ∨ 1066009856 = c ∨ 1066026240 = c ∨ 1066013952 = c ∨ 1066030336 = c ∨ 801767680 = c ∨ 801784064 = c ∨ 801771776 = c ∨ 801788160 = c ∨ 801768704 = c ∨ 801785088 = c ∨ 801772800 = c ∨ 801789184 = c ∨ 3475656960 = c ∨ 3475657984 = c ∨ 4289351936 = c ∨ 4289352960 = c ∨ 3392123312 = c ∨ 3392124336 = c ∨ False
  unfold endoTest test1249 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover1249 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1249 Point ⟨f⟩) : ∃ i, decode (codes1249 i) = f := by
  obtain ⟨i, hi⟩ := cover1249_bits (encode f) (endoTest_encode f he) (test1249_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

end Magma.UnaryTail0032

open Magma.UnaryTail0032

theorem Equation1249_not_termStructuralFromFin_Equation1263_unaryTail : ¬ Law1249.TermStructuralFromFin Law1263 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1263 i))
    (fun i => decode (codes1249 i)) source1263_injective
  · intro i
    exact (@Law1263.models_iff Point ⟨decode (codes1263 i)⟩).mpr (source1263_law i)
  · exact source1263_endo
  · intro f he h
    exact cover1249 f he ((@Law1249.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1249_not_termStructuralFromFin_Equation1263_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1249_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1249_not_termStructuralFromFin_Equation1263_unaryTail

