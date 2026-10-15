import equational_theories.Definability.FourPointTable

/-! Generated finite endomorphism obstruction. Small source lists are checked
in the kernel; bv_decide verifies that the target lists are exhaustive. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FourPointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma.UnaryTail1001

def step (x : Point) : Point := if x = 0 then 1 else if x = 1 then 0 else if x = 2 then 0 else 1

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

def codes109 : Fin 13 → Code := ![257578240, 1062884608, 261772544, 3482998016, 1067078912, 4288304384, 1063933184, 1068127488, 4289352960, 1063949568, 1068143872, 3482998064, 4288304432]

def codes443 : Fin 14 → Code := ![257578240, 3482998016, 1067078912, 4288304384, 1063933184, 1068127488, 4289352960, 1067095296, 1063949568, 1068143872, 3482998064, 1067078960, 4288304432, 1067095344]

def codes843 : Fin 17 → Code := ![257578240, 1062884608, 261772544, 3482998016, 1067078912, 4288304384, 1063933184, 1068127488, 4289352960, 1062900992, 1067095296, 1063949568, 1068143872, 261772592, 3482998064, 1067078960, 4288304432]

def codes1052 : Fin 25 → Code := ![257578240, 1062884608, 261772544, 3482998016, 1067078912, 4288304384, 1063933184, 1068127488, 4289352960, 257594624, 1062900992, 261788928, 1067095296, 1063949568, 1068143872, 257578288, 1062884656, 261772592, 3482998064, 1067078960, 4288304432, 257594672, 1062901040, 261788976, 1067095344]

def codes1056 : Fin 17 → Code := ![257578240, 1062884608, 261772544, 3482998016, 1067078912, 4288304384, 1063933184, 1068127488, 4289352960, 257594624, 261788928, 1063949568, 1068143872, 257578288, 1062884656, 3482998064, 4288304432]

def codes1253 : Fin 13 → Code := ![257578240, 1062884608, 261772544, 3482998016, 1067078912, 4288304384, 1063933184, 1068127488, 4289352960, 1063949568, 1068143872, 3482998064, 4288304432]

def codes1255 : Fin 13 → Code := ![257578240, 1062884608, 261772544, 3482998016, 1067078912, 4288304384, 1063933184, 1068127488, 4289352960, 1063949568, 1068143872, 3482998064, 4288304432]

def codes1263 : Fin 13 → Code := ![257578240, 1062884608, 261772544, 3482998016, 1067078912, 4288304384, 1063933184, 1068127488, 4289352960, 1063949568, 1068143872, 3482998064, 4288304432]

theorem source443_injective : Function.Injective (fun i => decode (codes443 i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes443 := by decide +kernel
  exact hi hc

theorem source443_law : ∀ i, @Equation443 Point ⟨decode (codes443 i)⟩ := by
  decide +kernel

theorem source443_endo : ∀ i, Commutes step (decode (codes443 i)) := by
  decide +kernel

theorem source1052_injective : Function.Injective (fun i => decode (codes1052 i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes1052 := by decide +kernel
  exact hi hc

theorem source1052_law : ∀ i, @Equation1052 Point ⟨decode (codes1052 i)⟩ := by
  decide +kernel

theorem source1052_endo : ∀ i, Commutes step (decode (codes1052 i)) := by
  decide +kernel

theorem source1056_injective : Function.Injective (fun i => decode (codes1056 i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes1056 := by decide +kernel
  exact hi hc

theorem source1056_law : ∀ i, @Equation1056 Point ⟨decode (codes1056 i)⟩ := by
  decide +kernel

theorem source1056_endo : ∀ i, Commutes step (decode (codes1056 i)) := by
  decide +kernel

def test109 (c : Code) : Prop :=
  0 = (decode c 0 (decode c (decode c 0 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c 0 0) 1)) ∧
  0 = (decode c 0 (decode c (decode c 0 0) 2)) ∧
  0 = (decode c 0 (decode c (decode c 0 0) 3)) ∧
  0 = (decode c 0 (decode c (decode c 1 1) 0)) ∧
  0 = (decode c 0 (decode c (decode c 1 1) 1)) ∧
  0 = (decode c 0 (decode c (decode c 1 1) 2)) ∧
  0 = (decode c 0 (decode c (decode c 1 1) 3)) ∧
  0 = (decode c 0 (decode c (decode c 2 2) 0)) ∧
  0 = (decode c 0 (decode c (decode c 2 2) 1)) ∧
  0 = (decode c 0 (decode c (decode c 2 2) 2)) ∧
  0 = (decode c 0 (decode c (decode c 2 2) 3)) ∧
  0 = (decode c 0 (decode c (decode c 3 3) 0)) ∧
  0 = (decode c 0 (decode c (decode c 3 3) 1)) ∧
  0 = (decode c 0 (decode c (decode c 3 3) 2)) ∧
  0 = (decode c 0 (decode c (decode c 3 3) 3)) ∧
  1 = (decode c 1 (decode c (decode c 0 0) 0)) ∧
  1 = (decode c 1 (decode c (decode c 0 0) 1)) ∧
  1 = (decode c 1 (decode c (decode c 0 0) 2)) ∧
  1 = (decode c 1 (decode c (decode c 0 0) 3)) ∧
  1 = (decode c 1 (decode c (decode c 1 1) 0)) ∧
  1 = (decode c 1 (decode c (decode c 1 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c 1 1) 2)) ∧
  1 = (decode c 1 (decode c (decode c 1 1) 3)) ∧
  1 = (decode c 1 (decode c (decode c 2 2) 0)) ∧
  1 = (decode c 1 (decode c (decode c 2 2) 1)) ∧
  1 = (decode c 1 (decode c (decode c 2 2) 2)) ∧
  1 = (decode c 1 (decode c (decode c 2 2) 3)) ∧
  1 = (decode c 1 (decode c (decode c 3 3) 0)) ∧
  1 = (decode c 1 (decode c (decode c 3 3) 1)) ∧
  1 = (decode c 1 (decode c (decode c 3 3) 2)) ∧
  1 = (decode c 1 (decode c (decode c 3 3) 3)) ∧
  2 = (decode c 2 (decode c (decode c 0 0) 0)) ∧
  2 = (decode c 2 (decode c (decode c 0 0) 1)) ∧
  2 = (decode c 2 (decode c (decode c 0 0) 2)) ∧
  2 = (decode c 2 (decode c (decode c 0 0) 3)) ∧
  2 = (decode c 2 (decode c (decode c 1 1) 0)) ∧
  2 = (decode c 2 (decode c (decode c 1 1) 1)) ∧
  2 = (decode c 2 (decode c (decode c 1 1) 2)) ∧
  2 = (decode c 2 (decode c (decode c 1 1) 3)) ∧
  2 = (decode c 2 (decode c (decode c 2 2) 0)) ∧
  2 = (decode c 2 (decode c (decode c 2 2) 1)) ∧
  2 = (decode c 2 (decode c (decode c 2 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c 2 2) 3)) ∧
  2 = (decode c 2 (decode c (decode c 3 3) 0)) ∧
  2 = (decode c 2 (decode c (decode c 3 3) 1)) ∧
  2 = (decode c 2 (decode c (decode c 3 3) 2)) ∧
  2 = (decode c 2 (decode c (decode c 3 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c 0 0) 0)) ∧
  3 = (decode c 3 (decode c (decode c 0 0) 1)) ∧
  3 = (decode c 3 (decode c (decode c 0 0) 2)) ∧
  3 = (decode c 3 (decode c (decode c 0 0) 3)) ∧
  3 = (decode c 3 (decode c (decode c 1 1) 0)) ∧
  3 = (decode c 3 (decode c (decode c 1 1) 1)) ∧
  3 = (decode c 3 (decode c (decode c 1 1) 2)) ∧
  3 = (decode c 3 (decode c (decode c 1 1) 3)) ∧
  3 = (decode c 3 (decode c (decode c 2 2) 0)) ∧
  3 = (decode c 3 (decode c (decode c 2 2) 1)) ∧
  3 = (decode c 3 (decode c (decode c 2 2) 2)) ∧
  3 = (decode c 3 (decode c (decode c 2 2) 3)) ∧
  3 = (decode c 3 (decode c (decode c 3 3) 0)) ∧
  3 = (decode c 3 (decode c (decode c 3 3) 1)) ∧
  3 = (decode c 3 (decode c (decode c 3 3) 2)) ∧
  3 = (decode c 3 (decode c (decode c 3 3) 3))

theorem test109_encode (f : Point → Point → Point) (h : @Equation109 Point ⟨f⟩) :
    test109 (encode f) := by
  unfold test109
  simp only [decode_encode]
  exact ⟨h 0 0 0, h 0 0 1, h 0 0 2, h 0 0 3, h 0 1 0, h 0 1 1, h 0 1 2, h 0 1 3, h 0 2 0, h 0 2 1, h 0 2 2, h 0 2 3, h 0 3 0, h 0 3 1, h 0 3 2, h 0 3 3, h 1 0 0, h 1 0 1, h 1 0 2, h 1 0 3, h 1 1 0, h 1 1 1, h 1 1 2, h 1 1 3, h 1 2 0, h 1 2 1, h 1 2 2, h 1 2 3, h 1 3 0, h 1 3 1, h 1 3 2, h 1 3 3, h 2 0 0, h 2 0 1, h 2 0 2, h 2 0 3, h 2 1 0, h 2 1 1, h 2 1 2, h 2 1 3, h 2 2 0, h 2 2 1, h 2 2 2, h 2 2 3, h 2 3 0, h 2 3 1, h 2 3 2, h 2 3 3, h 3 0 0, h 3 0 1, h 3 0 2, h 3 0 3, h 3 1 0, h 3 1 1, h 3 1 2, h 3 1 3, h 3 2 0, h 3 2 1, h 3 2 2, h 3 2 3, h 3 3 0, h 3 3 1, h 3 3 2, h 3 3 3⟩

theorem cover109_bits (c : Code) (he : endoTest c) (h : test109 c) :
    ∃ i, codes109 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes109, Fin.cons_zero,
    Fin.cons_succ]
  change 257578240 = c ∨ 1062884608 = c ∨ 261772544 = c ∨ 3482998016 = c ∨ 1067078912 = c ∨ 4288304384 = c ∨ 1063933184 = c ∨ 1068127488 = c ∨ 4289352960 = c ∨ 1063949568 = c ∨ 1068143872 = c ∨ 3482998064 = c ∨ 4288304432 = c ∨ False
  unfold endoTest test109 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover109 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation109 Point ⟨f⟩) : ∃ i, decode (codes109 i) = f := by
  obtain ⟨i, hi⟩ := cover109_bits (encode f) (endoTest_encode f he) (test109_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test843 (c : Code) : Prop :=
  0 = (decode c 0 (decode c (decode c 0 0) (decode c 0 0))) ∧
  0 = (decode c 0 (decode c (decode c 1 1) (decode c 0 1))) ∧
  0 = (decode c 0 (decode c (decode c 2 2) (decode c 0 2))) ∧
  0 = (decode c 0 (decode c (decode c 3 3) (decode c 0 3))) ∧
  1 = (decode c 1 (decode c (decode c 0 0) (decode c 1 0))) ∧
  1 = (decode c 1 (decode c (decode c 1 1) (decode c 1 1))) ∧
  1 = (decode c 1 (decode c (decode c 2 2) (decode c 1 2))) ∧
  1 = (decode c 1 (decode c (decode c 3 3) (decode c 1 3))) ∧
  2 = (decode c 2 (decode c (decode c 0 0) (decode c 2 0))) ∧
  2 = (decode c 2 (decode c (decode c 1 1) (decode c 2 1))) ∧
  2 = (decode c 2 (decode c (decode c 2 2) (decode c 2 2))) ∧
  2 = (decode c 2 (decode c (decode c 3 3) (decode c 2 3))) ∧
  3 = (decode c 3 (decode c (decode c 0 0) (decode c 3 0))) ∧
  3 = (decode c 3 (decode c (decode c 1 1) (decode c 3 1))) ∧
  3 = (decode c 3 (decode c (decode c 2 2) (decode c 3 2))) ∧
  3 = (decode c 3 (decode c (decode c 3 3) (decode c 3 3)))

theorem test843_encode (f : Point → Point → Point) (h : @Equation843 Point ⟨f⟩) :
    test843 (encode f) := by
  unfold test843
  simp only [decode_encode]
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 1 0, h 1 1, h 1 2, h 1 3, h 2 0, h 2 1, h 2 2, h 2 3, h 3 0, h 3 1, h 3 2, h 3 3⟩

theorem cover843_bits (c : Code) (he : endoTest c) (h : test843 c) :
    ∃ i, codes843 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes843, Fin.cons_zero,
    Fin.cons_succ]
  change 257578240 = c ∨ 1062884608 = c ∨ 261772544 = c ∨ 3482998016 = c ∨ 1067078912 = c ∨ 4288304384 = c ∨ 1063933184 = c ∨ 1068127488 = c ∨ 4289352960 = c ∨ 1062900992 = c ∨ 1067095296 = c ∨ 1063949568 = c ∨ 1068143872 = c ∨ 261772592 = c ∨ 3482998064 = c ∨ 1067078960 = c ∨ 4288304432 = c ∨ False
  unfold endoTest test843 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover843 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation843 Point ⟨f⟩) : ∃ i, decode (codes843 i) = f := by
  obtain ⟨i, hi⟩ := cover843_bits (encode f) (endoTest_encode f he) (test843_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test1253 (c : Code) : Prop :=
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 1) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 1) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 1) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 2) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 2) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 2) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 3) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 3) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 3) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 3) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 0) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 0) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 0) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 2) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 2) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 2) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 3) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 3) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 3) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 3) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 0) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 0) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 0) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 1) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 1) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 1) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 3) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 3) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 3) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 0) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 0) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 0) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 1) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 1) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 1) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 2) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 2) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 2) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 3))

theorem test1253_encode (f : Point → Point → Point) (h : @Equation1253 Point ⟨f⟩) :
    test1253 (encode f) := by
  unfold test1253
  simp only [decode_encode]
  exact ⟨h 0 0 0, h 0 0 1, h 0 0 2, h 0 0 3, h 0 1 0, h 0 1 1, h 0 1 2, h 0 1 3, h 0 2 0, h 0 2 1, h 0 2 2, h 0 2 3, h 0 3 0, h 0 3 1, h 0 3 2, h 0 3 3, h 1 0 0, h 1 0 1, h 1 0 2, h 1 0 3, h 1 1 0, h 1 1 1, h 1 1 2, h 1 1 3, h 1 2 0, h 1 2 1, h 1 2 2, h 1 2 3, h 1 3 0, h 1 3 1, h 1 3 2, h 1 3 3, h 2 0 0, h 2 0 1, h 2 0 2, h 2 0 3, h 2 1 0, h 2 1 1, h 2 1 2, h 2 1 3, h 2 2 0, h 2 2 1, h 2 2 2, h 2 2 3, h 2 3 0, h 2 3 1, h 2 3 2, h 2 3 3, h 3 0 0, h 3 0 1, h 3 0 2, h 3 0 3, h 3 1 0, h 3 1 1, h 3 1 2, h 3 1 3, h 3 2 0, h 3 2 1, h 3 2 2, h 3 2 3, h 3 3 0, h 3 3 1, h 3 3 2, h 3 3 3⟩

theorem cover1253_bits (c : Code) (he : endoTest c) (h : test1253 c) :
    ∃ i, codes1253 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes1253, Fin.cons_zero,
    Fin.cons_succ]
  change 257578240 = c ∨ 1062884608 = c ∨ 261772544 = c ∨ 3482998016 = c ∨ 1067078912 = c ∨ 4288304384 = c ∨ 1063933184 = c ∨ 1068127488 = c ∨ 4289352960 = c ∨ 1063949568 = c ∨ 1068143872 = c ∨ 3482998064 = c ∨ 4288304432 = c ∨ False
  unfold endoTest test1253 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover1253 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1253 Point ⟨f⟩) : ∃ i, decode (codes1253 i) = f := by
  obtain ⟨i, hi⟩ := cover1253_bits (encode f) (endoTest_encode f he) (test1253_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test1255 (c : Code) : Prop :=
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 1) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 2) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 3) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 0) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 2) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 3) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 0) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 1) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 3) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 0) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 1) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 2) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 3) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 1) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 2) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 3) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 0) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 2) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 3) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 0) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 1) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 3) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 0) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 1) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 2) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 3) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 1) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 2) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 3) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 0) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 2) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 3) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 0) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 1) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 3) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 0) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 1) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 2) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 1) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 2) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 3) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 0) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 2) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 3) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 0) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 1) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 3) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 0) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 1) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 2) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 3))

theorem test1255_encode (f : Point → Point → Point) (h : @Equation1255 Point ⟨f⟩) :
    test1255 (encode f) := by
  unfold test1255
  simp only [decode_encode]
  exact ⟨h 0 0 0, h 0 0 1, h 0 0 2, h 0 0 3, h 0 1 0, h 0 1 1, h 0 1 2, h 0 1 3, h 0 2 0, h 0 2 1, h 0 2 2, h 0 2 3, h 0 3 0, h 0 3 1, h 0 3 2, h 0 3 3, h 1 0 0, h 1 0 1, h 1 0 2, h 1 0 3, h 1 1 0, h 1 1 1, h 1 1 2, h 1 1 3, h 1 2 0, h 1 2 1, h 1 2 2, h 1 2 3, h 1 3 0, h 1 3 1, h 1 3 2, h 1 3 3, h 2 0 0, h 2 0 1, h 2 0 2, h 2 0 3, h 2 1 0, h 2 1 1, h 2 1 2, h 2 1 3, h 2 2 0, h 2 2 1, h 2 2 2, h 2 2 3, h 2 3 0, h 2 3 1, h 2 3 2, h 2 3 3, h 3 0 0, h 3 0 1, h 3 0 2, h 3 0 3, h 3 1 0, h 3 1 1, h 3 1 2, h 3 1 3, h 3 2 0, h 3 2 1, h 3 2 2, h 3 2 3, h 3 3 0, h 3 3 1, h 3 3 2, h 3 3 3⟩

theorem cover1255_bits (c : Code) (he : endoTest c) (h : test1255 c) :
    ∃ i, codes1255 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes1255, Fin.cons_zero,
    Fin.cons_succ]
  change 257578240 = c ∨ 1062884608 = c ∨ 261772544 = c ∨ 3482998016 = c ∨ 1067078912 = c ∨ 4288304384 = c ∨ 1063933184 = c ∨ 1068127488 = c ∨ 4289352960 = c ∨ 1063949568 = c ∨ 1068143872 = c ∨ 3482998064 = c ∨ 4288304432 = c ∨ False
  unfold endoTest test1255 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover1255 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1255 Point ⟨f⟩) : ∃ i, decode (codes1255 i) = f := by
  obtain ⟨i, hi⟩ := cover1255_bits (encode f) (endoTest_encode f he) (test1255_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test1263 (c : Code) : Prop :=
  0 = (decode c 0 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 1) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 2) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 0 3) 0) 0)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 0) 1) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 2) 1) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 1 3) 1) 1)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 0) 2) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 1) 2) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 2 3) 2) 2)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 0) 3) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 1) 3) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 2) 3) 3)) ∧
  0 = (decode c 0 (decode c (decode c (decode c 3 3) 3) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 1) 0) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 2) 0) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 0 3) 0) 0)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 0) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 2) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 1 3) 1) 1)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 0) 2) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 1) 2) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 2 3) 2) 2)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 0) 3) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 1) 3) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 2) 3) 3)) ∧
  1 = (decode c 1 (decode c (decode c (decode c 3 3) 3) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 1) 0) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 2) 0) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 0 3) 0) 0)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 0) 1) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 2) 1) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 1 3) 1) 1)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 0) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 1) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 2 3) 2) 2)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 0) 3) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 1) 3) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 2) 3) 3)) ∧
  2 = (decode c 2 (decode c (decode c (decode c 3 3) 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 0) 0) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 1) 0) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 2) 0) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 0 3) 0) 0)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 0) 1) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 1) 1) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 2) 1) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 1 3) 1) 1)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 0) 2) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 1) 2) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 2) 2) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 2 3) 2) 2)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 0) 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 1) 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 2) 3) 3)) ∧
  3 = (decode c 3 (decode c (decode c (decode c 3 3) 3) 3))

theorem test1263_encode (f : Point → Point → Point) (h : @Equation1263 Point ⟨f⟩) :
    test1263 (encode f) := by
  unfold test1263
  simp only [decode_encode]
  exact ⟨h 0 0 0, h 0 0 1, h 0 0 2, h 0 0 3, h 0 1 0, h 0 1 1, h 0 1 2, h 0 1 3, h 0 2 0, h 0 2 1, h 0 2 2, h 0 2 3, h 0 3 0, h 0 3 1, h 0 3 2, h 0 3 3, h 1 0 0, h 1 0 1, h 1 0 2, h 1 0 3, h 1 1 0, h 1 1 1, h 1 1 2, h 1 1 3, h 1 2 0, h 1 2 1, h 1 2 2, h 1 2 3, h 1 3 0, h 1 3 1, h 1 3 2, h 1 3 3, h 2 0 0, h 2 0 1, h 2 0 2, h 2 0 3, h 2 1 0, h 2 1 1, h 2 1 2, h 2 1 3, h 2 2 0, h 2 2 1, h 2 2 2, h 2 2 3, h 2 3 0, h 2 3 1, h 2 3 2, h 2 3 3, h 3 0 0, h 3 0 1, h 3 0 2, h 3 0 3, h 3 1 0, h 3 1 1, h 3 1 2, h 3 1 3, h 3 2 0, h 3 2 1, h 3 2 2, h 3 2 3, h 3 3 0, h 3 3 1, h 3 3 2, h 3 3 3⟩

theorem cover1263_bits (c : Code) (he : endoTest c) (h : test1263 c) :
    ∃ i, codes1263 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes1263, Fin.cons_zero,
    Fin.cons_succ]
  change 257578240 = c ∨ 1062884608 = c ∨ 261772544 = c ∨ 3482998016 = c ∨ 1067078912 = c ∨ 4288304384 = c ∨ 1063933184 = c ∨ 1068127488 = c ∨ 4289352960 = c ∨ 1063949568 = c ∨ 1068143872 = c ∨ 3482998064 = c ∨ 4288304432 = c ∨ False
  unfold endoTest test1263 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover1263 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1263 Point ⟨f⟩) : ∃ i, decode (codes1263 i) = f := by
  obtain ⟨i, hi⟩ := cover1263_bits (encode f) (endoTest_encode f he) (test1263_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

end Magma.UnaryTail1001

open Magma.UnaryTail1001

theorem Equation1253_not_termStructuralFromFin_Equation443_unaryTail : ¬ Law1253.TermStructuralFromFin Law443 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes443 i))
    (fun i => decode (codes1253 i)) source443_injective
  · intro i
    exact (@Law443.models_iff Point ⟨decode (codes443 i)⟩).mpr (source443_law i)
  · exact source443_endo
  · intro f he h
    exact cover1253 f he ((@Law1253.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1253_not_termStructuralFromFin_Equation443_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1253_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1253_not_termStructuralFromFin_Equation443_unaryTail

theorem Equation1255_not_termStructuralFromFin_Equation443_unaryTail : ¬ Law1255.TermStructuralFromFin Law443 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes443 i))
    (fun i => decode (codes1255 i)) source443_injective
  · intro i
    exact (@Law443.models_iff Point ⟨decode (codes443 i)⟩).mpr (source443_law i)
  · exact source443_endo
  · intro f he h
    exact cover1255 f he ((@Law1255.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1255_not_termStructuralFromFin_Equation443_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1255_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1255_not_termStructuralFromFin_Equation443_unaryTail

theorem Equation843_not_termStructuralFromFin_Equation1052_unaryTail : ¬ Law843.TermStructuralFromFin Law1052 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1052 i))
    (fun i => decode (codes843 i)) source1052_injective
  · intro i
    exact (@Law1052.models_iff Point ⟨decode (codes1052 i)⟩).mpr (source1052_law i)
  · exact source1052_endo
  · intro f he h
    exact cover843 f he ((@Law843.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation843_not_termStructuralFromFin_Equation1052_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover843_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation843_not_termStructuralFromFin_Equation1052_unaryTail

theorem Equation109_not_termStructuralFromFin_Equation1056_unaryTail : ¬ Law109.TermStructuralFromFin Law1056 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1056 i))
    (fun i => decode (codes109 i)) source1056_injective
  · intro i
    exact (@Law1056.models_iff Point ⟨decode (codes1056 i)⟩).mpr (source1056_law i)
  · exact source1056_endo
  · intro f he h
    exact cover109 f he ((@Law109.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation109_not_termStructuralFromFin_Equation1056_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover109_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation109_not_termStructuralFromFin_Equation1056_unaryTail

theorem Equation1253_not_termStructuralFromFin_Equation1056_unaryTail : ¬ Law1253.TermStructuralFromFin Law1056 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1056 i))
    (fun i => decode (codes1253 i)) source1056_injective
  · intro i
    exact (@Law1056.models_iff Point ⟨decode (codes1056 i)⟩).mpr (source1056_law i)
  · exact source1056_endo
  · intro f he h
    exact cover1253 f he ((@Law1253.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1253_not_termStructuralFromFin_Equation1056_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1253_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1253_not_termStructuralFromFin_Equation1056_unaryTail

theorem Equation1255_not_termStructuralFromFin_Equation1056_unaryTail : ¬ Law1255.TermStructuralFromFin Law1056 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1056 i))
    (fun i => decode (codes1255 i)) source1056_injective
  · intro i
    exact (@Law1056.models_iff Point ⟨decode (codes1056 i)⟩).mpr (source1056_law i)
  · exact source1056_endo
  · intro f he h
    exact cover1255 f he ((@Law1255.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1255_not_termStructuralFromFin_Equation1056_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1255_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1255_not_termStructuralFromFin_Equation1056_unaryTail

theorem Equation1263_not_termStructuralFromFin_Equation1056_unaryTail : ¬ Law1263.TermStructuralFromFin Law1056 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1056 i))
    (fun i => decode (codes1263 i)) source1056_injective
  · intro i
    exact (@Law1056.models_iff Point ⟨decode (codes1056 i)⟩).mpr (source1056_law i)
  · exact source1056_endo
  · intro f he h
    exact cover1263 f he ((@Law1263.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1263_not_termStructuralFromFin_Equation1056_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1263_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1263_not_termStructuralFromFin_Equation1056_unaryTail

