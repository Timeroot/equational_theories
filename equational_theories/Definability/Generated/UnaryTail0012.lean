import equational_theories.Definability.FourPointTable

/-! Generated finite endomorphism obstruction. Small source lists are checked
in the kernel; bv_decide verifies that the target lists are exhaustive. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FourPointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma.UnaryTail0012

def step (x : Point) : Point := if x = 0 then 0 else if x = 1 then 0 else if x = 2 then 1 else 2

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

def codes835 : Fin 18 → Code := ![1057620224, 1061814528, 1057636608, 1061830912, 1057620288, 1061814592, 1057636672, 1061830976, 1066012928, 1066029312, 1066012992, 1066029376, 1057653136, 1061847440, 1066045840, 4289352960, 3840206052, 1070260708]

def codes842 : Fin 18 → Code := ![1057620224, 1061814528, 1057636608, 1061830912, 1057620288, 1061814592, 1057636672, 1061830976, 1066012928, 1066029312, 1066012992, 1066029376, 1057653136, 1061847440, 1066045840, 4289352960, 3840206052, 1070260708]

def codes1252 : Fin 20 → Code := ![1057620224, 2131362048, 1061814528, 2135556352, 1057636608, 1061830912, 1057620288, 1061814592, 3206152448, 3210346752, 3206168832, 3210346816, 1066012928, 2139754752, 1066029312, 1066012992, 1057653136, 2131394960, 4289352960, 1070260708]

def codes1637 : Fin 18 → Code := ![4289352960, 12640484, 281075940, 79749348, 348184804, 29417700, 297853156, 96526564, 364962020, 549773540, 616882404, 566550756, 633659620, 180478180, 448913636, 717611236, 3840206052, 1070260708]

def codes3729 : Fin 18 → Code := ![0, 1057620224, 1061814528, 1057636608, 1061830912, 1057620288, 1061814592, 1057636672, 1061830976, 1066012928, 1066029312, 1066012992, 1066029376, 1057653136, 1061847440, 1066045840, 4289352960, 1070260708]

theorem source1252_injective : Function.Injective (fun i => decode (codes1252 i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes1252 := by decide +kernel
  exact hi hc

theorem source1252_law : ∀ i, @Equation1252 Point ⟨decode (codes1252 i)⟩ := by
  decide +kernel

theorem source1252_endo : ∀ i, Commutes step (decode (codes1252 i)) := by
  decide +kernel

def test835 (c : Code) : Prop :=
  0 = (decode c 0 (decode c (decode c 0 0) (decode c 0 0))) ∧
  0 = (decode c 0 (decode c (decode c 1 0) (decode c 1 0))) ∧
  0 = (decode c 0 (decode c (decode c 2 0) (decode c 2 0))) ∧
  0 = (decode c 0 (decode c (decode c 3 0) (decode c 3 0))) ∧
  1 = (decode c 1 (decode c (decode c 0 1) (decode c 0 1))) ∧
  1 = (decode c 1 (decode c (decode c 1 1) (decode c 1 1))) ∧
  1 = (decode c 1 (decode c (decode c 2 1) (decode c 2 1))) ∧
  1 = (decode c 1 (decode c (decode c 3 1) (decode c 3 1))) ∧
  2 = (decode c 2 (decode c (decode c 0 2) (decode c 0 2))) ∧
  2 = (decode c 2 (decode c (decode c 1 2) (decode c 1 2))) ∧
  2 = (decode c 2 (decode c (decode c 2 2) (decode c 2 2))) ∧
  2 = (decode c 2 (decode c (decode c 3 2) (decode c 3 2))) ∧
  3 = (decode c 3 (decode c (decode c 0 3) (decode c 0 3))) ∧
  3 = (decode c 3 (decode c (decode c 1 3) (decode c 1 3))) ∧
  3 = (decode c 3 (decode c (decode c 2 3) (decode c 2 3))) ∧
  3 = (decode c 3 (decode c (decode c 3 3) (decode c 3 3)))

theorem test835_encode (f : Point → Point → Point) (h : @Equation835 Point ⟨f⟩) :
    test835 (encode f) := by
  unfold test835
  simp only [decode_encode]
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 1 0, h 1 1, h 1 2, h 1 3, h 2 0, h 2 1, h 2 2, h 2 3, h 3 0, h 3 1, h 3 2, h 3 3⟩

theorem cover835_bits (c : Code) (he : endoTest c) (h : test835 c) :
    ∃ i, codes835 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes835, Fin.cons_zero,
    Fin.cons_succ]
  change 1057620224 = c ∨ 1061814528 = c ∨ 1057636608 = c ∨ 1061830912 = c ∨ 1057620288 = c ∨ 1061814592 = c ∨ 1057636672 = c ∨ 1061830976 = c ∨ 1066012928 = c ∨ 1066029312 = c ∨ 1066012992 = c ∨ 1066029376 = c ∨ 1057653136 = c ∨ 1061847440 = c ∨ 1066045840 = c ∨ 4289352960 = c ∨ 3840206052 = c ∨ 1070260708 = c ∨ False
  unfold endoTest test835 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover835 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation835 Point ⟨f⟩) : ∃ i, decode (codes835 i) = f := by
  obtain ⟨i, hi⟩ := cover835_bits (encode f) (endoTest_encode f he) (test835_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test842 (c : Code) : Prop :=
  0 = (decode c 0 (decode c (decode c 0 0) (decode c 0 0))) ∧
  0 = (decode c 0 (decode c (decode c 1 1) (decode c 0 0))) ∧
  0 = (decode c 0 (decode c (decode c 2 2) (decode c 0 0))) ∧
  0 = (decode c 0 (decode c (decode c 3 3) (decode c 0 0))) ∧
  1 = (decode c 1 (decode c (decode c 0 0) (decode c 1 1))) ∧
  1 = (decode c 1 (decode c (decode c 1 1) (decode c 1 1))) ∧
  1 = (decode c 1 (decode c (decode c 2 2) (decode c 1 1))) ∧
  1 = (decode c 1 (decode c (decode c 3 3) (decode c 1 1))) ∧
  2 = (decode c 2 (decode c (decode c 0 0) (decode c 2 2))) ∧
  2 = (decode c 2 (decode c (decode c 1 1) (decode c 2 2))) ∧
  2 = (decode c 2 (decode c (decode c 2 2) (decode c 2 2))) ∧
  2 = (decode c 2 (decode c (decode c 3 3) (decode c 2 2))) ∧
  3 = (decode c 3 (decode c (decode c 0 0) (decode c 3 3))) ∧
  3 = (decode c 3 (decode c (decode c 1 1) (decode c 3 3))) ∧
  3 = (decode c 3 (decode c (decode c 2 2) (decode c 3 3))) ∧
  3 = (decode c 3 (decode c (decode c 3 3) (decode c 3 3)))

theorem test842_encode (f : Point → Point → Point) (h : @Equation842 Point ⟨f⟩) :
    test842 (encode f) := by
  unfold test842
  simp only [decode_encode]
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 1 0, h 1 1, h 1 2, h 1 3, h 2 0, h 2 1, h 2 2, h 2 3, h 3 0, h 3 1, h 3 2, h 3 3⟩

theorem cover842_bits (c : Code) (he : endoTest c) (h : test842 c) :
    ∃ i, codes842 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes842, Fin.cons_zero,
    Fin.cons_succ]
  change 1057620224 = c ∨ 1061814528 = c ∨ 1057636608 = c ∨ 1061830912 = c ∨ 1057620288 = c ∨ 1061814592 = c ∨ 1057636672 = c ∨ 1061830976 = c ∨ 1066012928 = c ∨ 1066029312 = c ∨ 1066012992 = c ∨ 1066029376 = c ∨ 1057653136 = c ∨ 1061847440 = c ∨ 1066045840 = c ∨ 4289352960 = c ∨ 3840206052 = c ∨ 1070260708 = c ∨ False
  unfold endoTest test842 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover842 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation842 Point ⟨f⟩) : ∃ i, decode (codes842 i) = f := by
  obtain ⟨i, hi⟩ := cover842_bits (encode f) (endoTest_encode f he) (test842_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test1637 (c : Code) : Prop :=
  0 = (decode c (decode c 0 0) (decode c (decode c 0 0) 0)) ∧
  0 = (decode c (decode c 0 0) (decode c (decode c 1 1) 0)) ∧
  0 = (decode c (decode c 0 0) (decode c (decode c 2 2) 0)) ∧
  0 = (decode c (decode c 0 0) (decode c (decode c 3 3) 0)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 0 0) 1)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 1 1) 1)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 2 2) 1)) ∧
  1 = (decode c (decode c 1 1) (decode c (decode c 3 3) 1)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 0 0) 2)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 1 1) 2)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 2 2) 2)) ∧
  2 = (decode c (decode c 2 2) (decode c (decode c 3 3) 2)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 0 0) 3)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 1 1) 3)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 2 2) 3)) ∧
  3 = (decode c (decode c 3 3) (decode c (decode c 3 3) 3))

theorem test1637_encode (f : Point → Point → Point) (h : @Equation1637 Point ⟨f⟩) :
    test1637 (encode f) := by
  unfold test1637
  simp only [decode_encode]
  exact ⟨h 0 0, h 0 1, h 0 2, h 0 3, h 1 0, h 1 1, h 1 2, h 1 3, h 2 0, h 2 1, h 2 2, h 2 3, h 3 0, h 3 1, h 3 2, h 3 3⟩

theorem cover1637_bits (c : Code) (he : endoTest c) (h : test1637 c) :
    ∃ i, codes1637 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes1637, Fin.cons_zero,
    Fin.cons_succ]
  change 4289352960 = c ∨ 12640484 = c ∨ 281075940 = c ∨ 79749348 = c ∨ 348184804 = c ∨ 29417700 = c ∨ 297853156 = c ∨ 96526564 = c ∨ 364962020 = c ∨ 549773540 = c ∨ 616882404 = c ∨ 566550756 = c ∨ 633659620 = c ∨ 180478180 = c ∨ 448913636 = c ∨ 717611236 = c ∨ 3840206052 = c ∨ 1070260708 = c ∨ False
  unfold endoTest test1637 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover1637 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1637 Point ⟨f⟩) : ∃ i, decode (codes1637 i) = f := by
  obtain ⟨i, hi⟩ := cover1637_bits (encode f) (endoTest_encode f he) (test1637_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test3729 (c : Code) : Prop :=
  (decode c 0 0) = (decode c (decode c 0 0) (decode c 0 0)) ∧
  (decode c 0 0) = (decode c (decode c 0 0) (decode c 1 1)) ∧
  (decode c 0 0) = (decode c (decode c 0 0) (decode c 2 2)) ∧
  (decode c 0 0) = (decode c (decode c 0 0) (decode c 3 3)) ∧
  (decode c 0 1) = (decode c (decode c 0 1) (decode c 0 0)) ∧
  (decode c 0 1) = (decode c (decode c 0 1) (decode c 1 1)) ∧
  (decode c 0 1) = (decode c (decode c 0 1) (decode c 2 2)) ∧
  (decode c 0 1) = (decode c (decode c 0 1) (decode c 3 3)) ∧
  (decode c 0 2) = (decode c (decode c 0 2) (decode c 0 0)) ∧
  (decode c 0 2) = (decode c (decode c 0 2) (decode c 1 1)) ∧
  (decode c 0 2) = (decode c (decode c 0 2) (decode c 2 2)) ∧
  (decode c 0 2) = (decode c (decode c 0 2) (decode c 3 3)) ∧
  (decode c 0 3) = (decode c (decode c 0 3) (decode c 0 0)) ∧
  (decode c 0 3) = (decode c (decode c 0 3) (decode c 1 1)) ∧
  (decode c 0 3) = (decode c (decode c 0 3) (decode c 2 2)) ∧
  (decode c 0 3) = (decode c (decode c 0 3) (decode c 3 3)) ∧
  (decode c 1 0) = (decode c (decode c 1 0) (decode c 0 0)) ∧
  (decode c 1 0) = (decode c (decode c 1 0) (decode c 1 1)) ∧
  (decode c 1 0) = (decode c (decode c 1 0) (decode c 2 2)) ∧
  (decode c 1 0) = (decode c (decode c 1 0) (decode c 3 3)) ∧
  (decode c 1 1) = (decode c (decode c 1 1) (decode c 0 0)) ∧
  (decode c 1 1) = (decode c (decode c 1 1) (decode c 1 1)) ∧
  (decode c 1 1) = (decode c (decode c 1 1) (decode c 2 2)) ∧
  (decode c 1 1) = (decode c (decode c 1 1) (decode c 3 3)) ∧
  (decode c 1 2) = (decode c (decode c 1 2) (decode c 0 0)) ∧
  (decode c 1 2) = (decode c (decode c 1 2) (decode c 1 1)) ∧
  (decode c 1 2) = (decode c (decode c 1 2) (decode c 2 2)) ∧
  (decode c 1 2) = (decode c (decode c 1 2) (decode c 3 3)) ∧
  (decode c 1 3) = (decode c (decode c 1 3) (decode c 0 0)) ∧
  (decode c 1 3) = (decode c (decode c 1 3) (decode c 1 1)) ∧
  (decode c 1 3) = (decode c (decode c 1 3) (decode c 2 2)) ∧
  (decode c 1 3) = (decode c (decode c 1 3) (decode c 3 3)) ∧
  (decode c 2 0) = (decode c (decode c 2 0) (decode c 0 0)) ∧
  (decode c 2 0) = (decode c (decode c 2 0) (decode c 1 1)) ∧
  (decode c 2 0) = (decode c (decode c 2 0) (decode c 2 2)) ∧
  (decode c 2 0) = (decode c (decode c 2 0) (decode c 3 3)) ∧
  (decode c 2 1) = (decode c (decode c 2 1) (decode c 0 0)) ∧
  (decode c 2 1) = (decode c (decode c 2 1) (decode c 1 1)) ∧
  (decode c 2 1) = (decode c (decode c 2 1) (decode c 2 2)) ∧
  (decode c 2 1) = (decode c (decode c 2 1) (decode c 3 3)) ∧
  (decode c 2 2) = (decode c (decode c 2 2) (decode c 0 0)) ∧
  (decode c 2 2) = (decode c (decode c 2 2) (decode c 1 1)) ∧
  (decode c 2 2) = (decode c (decode c 2 2) (decode c 2 2)) ∧
  (decode c 2 2) = (decode c (decode c 2 2) (decode c 3 3)) ∧
  (decode c 2 3) = (decode c (decode c 2 3) (decode c 0 0)) ∧
  (decode c 2 3) = (decode c (decode c 2 3) (decode c 1 1)) ∧
  (decode c 2 3) = (decode c (decode c 2 3) (decode c 2 2)) ∧
  (decode c 2 3) = (decode c (decode c 2 3) (decode c 3 3)) ∧
  (decode c 3 0) = (decode c (decode c 3 0) (decode c 0 0)) ∧
  (decode c 3 0) = (decode c (decode c 3 0) (decode c 1 1)) ∧
  (decode c 3 0) = (decode c (decode c 3 0) (decode c 2 2)) ∧
  (decode c 3 0) = (decode c (decode c 3 0) (decode c 3 3)) ∧
  (decode c 3 1) = (decode c (decode c 3 1) (decode c 0 0)) ∧
  (decode c 3 1) = (decode c (decode c 3 1) (decode c 1 1)) ∧
  (decode c 3 1) = (decode c (decode c 3 1) (decode c 2 2)) ∧
  (decode c 3 1) = (decode c (decode c 3 1) (decode c 3 3)) ∧
  (decode c 3 2) = (decode c (decode c 3 2) (decode c 0 0)) ∧
  (decode c 3 2) = (decode c (decode c 3 2) (decode c 1 1)) ∧
  (decode c 3 2) = (decode c (decode c 3 2) (decode c 2 2)) ∧
  (decode c 3 2) = (decode c (decode c 3 2) (decode c 3 3)) ∧
  (decode c 3 3) = (decode c (decode c 3 3) (decode c 0 0)) ∧
  (decode c 3 3) = (decode c (decode c 3 3) (decode c 1 1)) ∧
  (decode c 3 3) = (decode c (decode c 3 3) (decode c 2 2)) ∧
  (decode c 3 3) = (decode c (decode c 3 3) (decode c 3 3))

theorem test3729_encode (f : Point → Point → Point) (h : @Equation3729 Point ⟨f⟩) :
    test3729 (encode f) := by
  unfold test3729
  simp only [decode_encode]
  exact ⟨h 0 0 0, h 0 0 1, h 0 0 2, h 0 0 3, h 0 1 0, h 0 1 1, h 0 1 2, h 0 1 3, h 0 2 0, h 0 2 1, h 0 2 2, h 0 2 3, h 0 3 0, h 0 3 1, h 0 3 2, h 0 3 3, h 1 0 0, h 1 0 1, h 1 0 2, h 1 0 3, h 1 1 0, h 1 1 1, h 1 1 2, h 1 1 3, h 1 2 0, h 1 2 1, h 1 2 2, h 1 2 3, h 1 3 0, h 1 3 1, h 1 3 2, h 1 3 3, h 2 0 0, h 2 0 1, h 2 0 2, h 2 0 3, h 2 1 0, h 2 1 1, h 2 1 2, h 2 1 3, h 2 2 0, h 2 2 1, h 2 2 2, h 2 2 3, h 2 3 0, h 2 3 1, h 2 3 2, h 2 3 3, h 3 0 0, h 3 0 1, h 3 0 2, h 3 0 3, h 3 1 0, h 3 1 1, h 3 1 2, h 3 1 3, h 3 2 0, h 3 2 1, h 3 2 2, h 3 2 3, h 3 3 0, h 3 3 1, h 3 3 2, h 3 3 3⟩

theorem cover3729_bits (c : Code) (he : endoTest c) (h : test3729 c) :
    ∃ i, codes3729 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes3729, Fin.cons_zero,
    Fin.cons_succ]
  change 0 = c ∨ 1057620224 = c ∨ 1061814528 = c ∨ 1057636608 = c ∨ 1061830912 = c ∨ 1057620288 = c ∨ 1061814592 = c ∨ 1057636672 = c ∨ 1061830976 = c ∨ 1066012928 = c ∨ 1066029312 = c ∨ 1066012992 = c ∨ 1066029376 = c ∨ 1057653136 = c ∨ 1061847440 = c ∨ 1066045840 = c ∨ 4289352960 = c ∨ 1070260708 = c ∨ False
  unfold endoTest test3729 decode step at *
  bv_decide (config := { timeout := 60 })

theorem cover3729 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation3729 Point ⟨f⟩) : ∃ i, decode (codes3729 i) = f := by
  obtain ⟨i, hi⟩ := cover3729_bits (encode f) (endoTest_encode f he) (test3729_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

end Magma.UnaryTail0012

open Magma.UnaryTail0012

theorem Equation835_not_termStructuralFromFin_Equation1252_unaryTail : ¬ Law835.TermStructuralFromFin Law1252 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1252 i))
    (fun i => decode (codes835 i)) source1252_injective
  · intro i
    exact (@Law1252.models_iff Point ⟨decode (codes1252 i)⟩).mpr (source1252_law i)
  · exact source1252_endo
  · intro f he h
    exact cover835 f he ((@Law835.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation835_not_termStructuralFromFin_Equation1252_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover835_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation835_not_termStructuralFromFin_Equation1252_unaryTail

theorem Equation842_not_termStructuralFromFin_Equation1252_unaryTail : ¬ Law842.TermStructuralFromFin Law1252 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1252 i))
    (fun i => decode (codes842 i)) source1252_injective
  · intro i
    exact (@Law1252.models_iff Point ⟨decode (codes1252 i)⟩).mpr (source1252_law i)
  · exact source1252_endo
  · intro f he h
    exact cover842 f he ((@Law842.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation842_not_termStructuralFromFin_Equation1252_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover842_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation842_not_termStructuralFromFin_Equation1252_unaryTail

theorem Equation1637_not_termStructuralFromFin_Equation1252_unaryTail : ¬ Law1637.TermStructuralFromFin Law1252 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1252 i))
    (fun i => decode (codes1637 i)) source1252_injective
  · intro i
    exact (@Law1252.models_iff Point ⟨decode (codes1252 i)⟩).mpr (source1252_law i)
  · exact source1252_endo
  · intro f he h
    exact cover1637 f he ((@Law1637.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1637_not_termStructuralFromFin_Equation1252_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1637_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1637_not_termStructuralFromFin_Equation1252_unaryTail

theorem Equation3729_not_termStructuralFromFin_Equation1252_unaryTail : ¬ Law3729.TermStructuralFromFin Law1252 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes1252 i))
    (fun i => decode (codes3729 i)) source1252_injective
  · intro i
    exact (@Law1252.models_iff Point ⟨decode (codes1252 i)⟩).mpr (source1252_law i)
  · exact source1252_endo
  · intro f he h
    exact cover3729 f he ((@Law3729.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation3729_not_termStructuralFromFin_Equation1252_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover3729_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3729_not_termStructuralFromFin_Equation1252_unaryTail

