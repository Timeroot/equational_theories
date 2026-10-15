import equational_theories.Definability.FivePointTable

/-! Generated finite endomorphism obstruction. Source tables are checked in
Lean's kernel; target-list completeness uses the standard bv_decide checker. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FivePointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Magma.UnaryTail02311

def step (x : Point) : Point := ![0, 2, 3, 1, 1] x
def stepBits (x : BitVec 3) : BitVec 3 := if x = 0 then 0 else if x = 1 then 2 else if x = 2 then 3 else if x = 3 then 1 else 1

theorem step_point (x : Point) : stepBits (point x) = point (step x) := by
  fin_cases x <;> rfl

def endoTest (c : Code) : Prop :=
  bits c (stepBits 0) (stepBits 0) = stepBits (bits c 0 0) ∧
  bits c (stepBits 0) (stepBits 1) = stepBits (bits c 0 1) ∧
  bits c (stepBits 0) (stepBits 2) = stepBits (bits c 0 2) ∧
  bits c (stepBits 0) (stepBits 3) = stepBits (bits c 0 3) ∧
  bits c (stepBits 0) (stepBits 4) = stepBits (bits c 0 4) ∧
  bits c (stepBits 1) (stepBits 0) = stepBits (bits c 1 0) ∧
  bits c (stepBits 1) (stepBits 1) = stepBits (bits c 1 1) ∧
  bits c (stepBits 1) (stepBits 2) = stepBits (bits c 1 2) ∧
  bits c (stepBits 1) (stepBits 3) = stepBits (bits c 1 3) ∧
  bits c (stepBits 1) (stepBits 4) = stepBits (bits c 1 4) ∧
  bits c (stepBits 2) (stepBits 0) = stepBits (bits c 2 0) ∧
  bits c (stepBits 2) (stepBits 1) = stepBits (bits c 2 1) ∧
  bits c (stepBits 2) (stepBits 2) = stepBits (bits c 2 2) ∧
  bits c (stepBits 2) (stepBits 3) = stepBits (bits c 2 3) ∧
  bits c (stepBits 2) (stepBits 4) = stepBits (bits c 2 4) ∧
  bits c (stepBits 3) (stepBits 0) = stepBits (bits c 3 0) ∧
  bits c (stepBits 3) (stepBits 1) = stepBits (bits c 3 1) ∧
  bits c (stepBits 3) (stepBits 2) = stepBits (bits c 3 2) ∧
  bits c (stepBits 3) (stepBits 3) = stepBits (bits c 3 3) ∧
  bits c (stepBits 3) (stepBits 4) = stepBits (bits c 3 4) ∧
  bits c (stepBits 4) (stepBits 0) = stepBits (bits c 4 0) ∧
  bits c (stepBits 4) (stepBits 1) = stepBits (bits c 4 1) ∧
  bits c (stepBits 4) (stepBits 2) = stepBits (bits c 4 2) ∧
  bits c (stepBits 4) (stepBits 3) = stepBits (bits c 4 3) ∧
  bits c (stepBits 4) (stepBits 4) = stepBits (bits c 4 4)

theorem endoTest_encode (f : Point → Point → Point) (h : Commutes step f) :
    endoTest (encode f) := by
  have hh (x y : Point) : bits (encode f) (stepBits (point x)) (stepBits (point y)) =
      stepBits (bits (encode f) (point x) (point y)) := by
    rw [step_point, step_point, bits_encode, bits_encode, step_point]
    exact congrArg point (h x y)
  exact ⟨hh 0 0, hh 0 1, hh 0 2, hh 0 3, hh 0 4, hh 1 0, hh 1 1, hh 1 2, hh 1 3, hh 1 4, hh 2 0, hh 2 1, hh 2 2, hh 2 3, hh 2 4, hh 3 0, hh 3 1, hh 3 2, hh 3 3, hh 3 4, hh 4 0, hh 4 1, hh 4 2, hh 4 3, hh 4 4⟩

def codes626 : Fin 25 → Code := ![21255747353384289861632, 21477115037685576400896, 21550902013980414607360, 21283418323815391068160, 21292641695852245843968, 21503633086612070760448, 21577420062906908966912, 21512856458648925536256, 21586643434943763742720, 21504786008116677607424, 21578572984411515813888, 21514009380153532383232, 21587796356448370589696, 21365278002468362682368, 21366430923972969529344, 21568196404447279349760, 21569349325951886196736, 38047299160156209152, 21510550545272041439232, 21584337521566879645696, 21362972089091478585344, 297460573975156457472, 21576267106216856354816, 21585490478253711130624, 21567043447757226737664]

def codes1478 : Fin 23 → Code := ![20660983866639968913032, 20808562322838315615880, 20808562322838449833608, 20670207534995211568776, 20670207539393258079880, 20743996767513981761160, 20743996767513981765256, 20817785991193558267528, 20817785995591604778632, 20817785991193692485256, 20817785995591738996360, 20817785991193558271624, 20817785995591604782728, 20817785991193692489352, 20817785995591739000456, 20827009634809921418888, 20827009634809921422984, 20817785991193692476112, 20817785995591738987216, 20827009634809921409744, 20743996767513981756504, 20817785995591604773976, 20817785995591738991704]

def codes1630 : Fin 23 → Code := ![21255747353384289861632, 21477115037685576400896, 21550902013980414607360, 21283418323815391068160, 21292641695852245843968, 21503633086612070760448, 21577420062906908966912, 21512856458648925536256, 21586643434943763742720, 21504786008116677607424, 21578572984411515813888, 21514009380153532383232, 21587796356448370589696, 21365278002468362682368, 21366430923972969529344, 21568196404447279349760, 21569349325951886196736, 21510550545272041439232, 21584337521566879645696, 21362972089091478585344, 21576267106216856354816, 21585490478253711130624, 21567043447757226737664]

def codes1681 : Fin 23 → Code := ![20660983866639968913032, 20808562322838315615880, 20808562322838449833608, 20670207534995211568776, 20670207539393258079880, 20743996767513981761160, 20743996767513981765256, 20817785991193558267528, 20817785995591604778632, 20817785991193692485256, 20817785995591738996360, 20817785991193558271624, 20817785995591604782728, 20817785991193692489352, 20817785995591739000456, 20827009634809921418888, 20827009634809921422984, 20817785991193692476112, 20817785995591738987216, 20827009634809921409744, 20743996767513981756504, 20817785995591604773976, 20817785995591738991704]

theorem source626_injective : Function.Injective (fun i => decode (codes626 i)) := by
  decide +kernel

theorem source626_law : ∀ i, @Equation626 Point ⟨decode (codes626 i)⟩ := by
  decide +kernel

theorem source626_endo : ∀ i, Commutes step (decode (codes626 i)) := by
  decide +kernel

def test1478 (c : Code) : Prop :=
  0 = (bits c (bits c 0 0) (bits c 0 (bits c 0 0))) ∧
  0 = (bits c (bits c 1 0) (bits c 0 (bits c 0 0))) ∧
  0 = (bits c (bits c 2 0) (bits c 0 (bits c 0 0))) ∧
  0 = (bits c (bits c 3 0) (bits c 0 (bits c 0 0))) ∧
  0 = (bits c (bits c 4 0) (bits c 0 (bits c 0 0))) ∧
  1 = (bits c (bits c 0 1) (bits c 1 (bits c 1 1))) ∧
  1 = (bits c (bits c 1 1) (bits c 1 (bits c 1 1))) ∧
  1 = (bits c (bits c 2 1) (bits c 1 (bits c 1 1))) ∧
  1 = (bits c (bits c 3 1) (bits c 1 (bits c 1 1))) ∧
  1 = (bits c (bits c 4 1) (bits c 1 (bits c 1 1))) ∧
  2 = (bits c (bits c 0 2) (bits c 2 (bits c 2 2))) ∧
  2 = (bits c (bits c 1 2) (bits c 2 (bits c 2 2))) ∧
  2 = (bits c (bits c 2 2) (bits c 2 (bits c 2 2))) ∧
  2 = (bits c (bits c 3 2) (bits c 2 (bits c 2 2))) ∧
  2 = (bits c (bits c 4 2) (bits c 2 (bits c 2 2))) ∧
  3 = (bits c (bits c 0 3) (bits c 3 (bits c 3 3))) ∧
  3 = (bits c (bits c 1 3) (bits c 3 (bits c 3 3))) ∧
  3 = (bits c (bits c 2 3) (bits c 3 (bits c 3 3))) ∧
  3 = (bits c (bits c 3 3) (bits c 3 (bits c 3 3))) ∧
  3 = (bits c (bits c 4 3) (bits c 3 (bits c 3 3))) ∧
  4 = (bits c (bits c 0 4) (bits c 4 (bits c 4 4))) ∧
  4 = (bits c (bits c 1 4) (bits c 4 (bits c 4 4))) ∧
  4 = (bits c (bits c 2 4) (bits c 4 (bits c 4 4))) ∧
  4 = (bits c (bits c 3 4) (bits c 4 (bits c 4 4))) ∧
  4 = (bits c (bits c 4 4) (bits c 4 (bits c 4 4)))

theorem test1478_encode (f : Point → Point → Point) (h : @Equation1478 Point ⟨f⟩) :
    test1478 (encode f) := by
  have hh (x y : Point) :
    (point x) = (bits (encode f) (bits (encode f) (point y) (point x)) (bits (encode f) (point x) (bits (encode f) (point x) (point x)))) := by
    simp only [bits_encode]
    exact congrArg point (h x y)
  exact ⟨hh 0 0, hh 0 1, hh 0 2, hh 0 3, hh 0 4, hh 1 0, hh 1 1, hh 1 2, hh 1 3, hh 1 4, hh 2 0, hh 2 1, hh 2 2, hh 2 3, hh 2 4, hh 3 0, hh 3 1, hh 3 2, hh 3 3, hh 3 4, hh 4 0, hh 4 1, hh 4 2, hh 4 3, hh 4 4⟩

theorem cover1478_bits (c : Code) (hv : Valid c) (he : endoTest c) (h : test1478 c) :
    ∃ i, codes1478 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero]
  change 20660983866639968913032 = c ∨ 20808562322838315615880 = c ∨ 20808562322838449833608 = c ∨ 20670207534995211568776 = c ∨ 20670207539393258079880 = c ∨ 20743996767513981761160 = c ∨ 20743996767513981765256 = c ∨ 20817785991193558267528 = c ∨ 20817785995591604778632 = c ∨ 20817785991193692485256 = c ∨ 20817785995591738996360 = c ∨ 20817785991193558271624 = c ∨ 20817785995591604782728 = c ∨ 20817785991193692489352 = c ∨ 20817785995591739000456 = c ∨ 20827009634809921418888 = c ∨ 20827009634809921422984 = c ∨ 20817785991193692476112 = c ∨ 20817785995591738987216 = c ∨ 20827009634809921409744 = c ∨ 20743996767513981756504 = c ∨ 20817785995591604773976 = c ∨ 20817785995591738991704 = c ∨ False
  unfold Valid endoTest test1478 bits stepBits at *
  bv_decide (config := { timeout := 60 })

theorem cover1478 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1478 Point ⟨f⟩) : ∃ i, decode (codes1478 i) = f := by
  obtain ⟨i, hi⟩ := cover1478_bits (encode f) (valid_encode f)
    (endoTest_encode f he) (test1478_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test1630 (c : Code) : Prop :=
  0 = (bits c (bits c 0 0) (bits c (bits c 0 0) 0)) ∧
  0 = (bits c (bits c 0 0) (bits c (bits c 0 0) 1)) ∧
  0 = (bits c (bits c 0 0) (bits c (bits c 0 0) 2)) ∧
  0 = (bits c (bits c 0 0) (bits c (bits c 0 0) 3)) ∧
  0 = (bits c (bits c 0 0) (bits c (bits c 0 0) 4)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 1) 0)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 1) 1)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 1) 2)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 1) 3)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 1) 4)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 2) 0)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 2) 1)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 2) 2)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 2) 3)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 2) 4)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 3) 0)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 3) 1)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 3) 2)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 3) 3)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 3) 4)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 4) 0)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 4) 1)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 4) 2)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 4) 3)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 4) 4))

theorem test1630_encode (f : Point → Point → Point) (h : @Equation1630 Point ⟨f⟩) :
    test1630 (encode f) := by
  have hh (x y : Point) :
    (point x) = (bits (encode f) (bits (encode f) (point x) (point x)) (bits (encode f) (bits (encode f) (point x) (point x)) (point y))) := by
    simp only [bits_encode]
    exact congrArg point (h x y)
  exact ⟨hh 0 0, hh 0 1, hh 0 2, hh 0 3, hh 0 4, hh 1 0, hh 1 1, hh 1 2, hh 1 3, hh 1 4, hh 2 0, hh 2 1, hh 2 2, hh 2 3, hh 2 4, hh 3 0, hh 3 1, hh 3 2, hh 3 3, hh 3 4, hh 4 0, hh 4 1, hh 4 2, hh 4 3, hh 4 4⟩

theorem cover1630_bits (c : Code) (hv : Valid c) (he : endoTest c) (h : test1630 c) :
    ∃ i, codes1630 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero]
  change 21255747353384289861632 = c ∨ 21477115037685576400896 = c ∨ 21550902013980414607360 = c ∨ 21283418323815391068160 = c ∨ 21292641695852245843968 = c ∨ 21503633086612070760448 = c ∨ 21577420062906908966912 = c ∨ 21512856458648925536256 = c ∨ 21586643434943763742720 = c ∨ 21504786008116677607424 = c ∨ 21578572984411515813888 = c ∨ 21514009380153532383232 = c ∨ 21587796356448370589696 = c ∨ 21365278002468362682368 = c ∨ 21366430923972969529344 = c ∨ 21568196404447279349760 = c ∨ 21569349325951886196736 = c ∨ 21510550545272041439232 = c ∨ 21584337521566879645696 = c ∨ 21362972089091478585344 = c ∨ 21576267106216856354816 = c ∨ 21585490478253711130624 = c ∨ 21567043447757226737664 = c ∨ False
  unfold Valid endoTest test1630 bits stepBits at *
  bv_decide (config := { timeout := 60 })

theorem cover1630 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1630 Point ⟨f⟩) : ∃ i, decode (codes1630 i) = f := by
  obtain ⟨i, hi⟩ := cover1630_bits (encode f) (valid_encode f)
    (endoTest_encode f he) (test1630_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

def test1681 (c : Code) : Prop :=
  0 = (bits c (bits c 0 0) (bits c (bits c 0 0) 0)) ∧
  0 = (bits c (bits c 1 0) (bits c (bits c 0 0) 0)) ∧
  0 = (bits c (bits c 2 0) (bits c (bits c 0 0) 0)) ∧
  0 = (bits c (bits c 3 0) (bits c (bits c 0 0) 0)) ∧
  0 = (bits c (bits c 4 0) (bits c (bits c 0 0) 0)) ∧
  1 = (bits c (bits c 0 1) (bits c (bits c 1 1) 1)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 1) 1)) ∧
  1 = (bits c (bits c 2 1) (bits c (bits c 1 1) 1)) ∧
  1 = (bits c (bits c 3 1) (bits c (bits c 1 1) 1)) ∧
  1 = (bits c (bits c 4 1) (bits c (bits c 1 1) 1)) ∧
  2 = (bits c (bits c 0 2) (bits c (bits c 2 2) 2)) ∧
  2 = (bits c (bits c 1 2) (bits c (bits c 2 2) 2)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 2) 2)) ∧
  2 = (bits c (bits c 3 2) (bits c (bits c 2 2) 2)) ∧
  2 = (bits c (bits c 4 2) (bits c (bits c 2 2) 2)) ∧
  3 = (bits c (bits c 0 3) (bits c (bits c 3 3) 3)) ∧
  3 = (bits c (bits c 1 3) (bits c (bits c 3 3) 3)) ∧
  3 = (bits c (bits c 2 3) (bits c (bits c 3 3) 3)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 3) 3)) ∧
  3 = (bits c (bits c 4 3) (bits c (bits c 3 3) 3)) ∧
  4 = (bits c (bits c 0 4) (bits c (bits c 4 4) 4)) ∧
  4 = (bits c (bits c 1 4) (bits c (bits c 4 4) 4)) ∧
  4 = (bits c (bits c 2 4) (bits c (bits c 4 4) 4)) ∧
  4 = (bits c (bits c 3 4) (bits c (bits c 4 4) 4)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 4) 4))

theorem test1681_encode (f : Point → Point → Point) (h : @Equation1681 Point ⟨f⟩) :
    test1681 (encode f) := by
  have hh (x y : Point) :
    (point x) = (bits (encode f) (bits (encode f) (point y) (point x)) (bits (encode f) (bits (encode f) (point x) (point x)) (point x))) := by
    simp only [bits_encode]
    exact congrArg point (h x y)
  exact ⟨hh 0 0, hh 0 1, hh 0 2, hh 0 3, hh 0 4, hh 1 0, hh 1 1, hh 1 2, hh 1 3, hh 1 4, hh 2 0, hh 2 1, hh 2 2, hh 2 3, hh 2 4, hh 3 0, hh 3 1, hh 3 2, hh 3 3, hh 3 4, hh 4 0, hh 4 1, hh 4 2, hh 4 3, hh 4 4⟩

theorem cover1681_bits (c : Code) (hv : Valid c) (he : endoTest c) (h : test1681 c) :
    ∃ i, codes1681 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero]
  change 20660983866639968913032 = c ∨ 20808562322838315615880 = c ∨ 20808562322838449833608 = c ∨ 20670207534995211568776 = c ∨ 20670207539393258079880 = c ∨ 20743996767513981761160 = c ∨ 20743996767513981765256 = c ∨ 20817785991193558267528 = c ∨ 20817785995591604778632 = c ∨ 20817785991193692485256 = c ∨ 20817785995591738996360 = c ∨ 20817785991193558271624 = c ∨ 20817785995591604782728 = c ∨ 20817785991193692489352 = c ∨ 20817785995591739000456 = c ∨ 20827009634809921418888 = c ∨ 20827009634809921422984 = c ∨ 20817785991193692476112 = c ∨ 20817785995591738987216 = c ∨ 20827009634809921409744 = c ∨ 20743996767513981756504 = c ∨ 20817785995591604773976 = c ∨ 20817785995591738991704 = c ∨ False
  unfold Valid endoTest test1681 bits stepBits at *
  bv_decide (config := { timeout := 60 })

theorem cover1681 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1681 Point ⟨f⟩) : ∃ i, decode (codes1681 i) = f := by
  obtain ⟨i, hi⟩ := cover1681_bits (encode f) (valid_encode f)
    (endoTest_encode f he) (test1681_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

end Magma.UnaryTail02311

open Magma.UnaryTail02311

theorem Equation1478_not_termStructuralFromFin_Equation626_unaryTail : ¬ Law1478.TermStructuralFromFin Law626 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes626 i))
    (fun i => decode (codes1478 i)) source626_injective
  · intro i
    exact (@Law626.models_iff Point ⟨decode (codes626 i)⟩).mpr (source626_law i)
  · exact source626_endo
  · intro f he h
    exact cover1478 f he ((@Law1478.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1478_not_termStructuralFromFin_Equation626_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1478_bits._native.bv_decide.ax_1_7] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1478_not_termStructuralFromFin_Equation626_unaryTail

theorem Equation1630_not_termStructuralFromFin_Equation626_unaryTail : ¬ Law1630.TermStructuralFromFin Law626 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes626 i))
    (fun i => decode (codes1630 i)) source626_injective
  · intro i
    exact (@Law626.models_iff Point ⟨decode (codes626 i)⟩).mpr (source626_law i)
  · exact source626_endo
  · intro f he h
    exact cover1630 f he ((@Law1630.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1630_not_termStructuralFromFin_Equation626_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1630_bits._native.bv_decide.ax_1_7] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1630_not_termStructuralFromFin_Equation626_unaryTail

theorem Equation1681_not_termStructuralFromFin_Equation626_unaryTail : ¬ Law1681.TermStructuralFromFin Law626 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes626 i))
    (fun i => decode (codes1681 i)) source626_injective
  · intro i
    exact (@Law626.models_iff Point ⟨decode (codes626 i)⟩).mpr (source626_law i)
  · exact source626_endo
  · intro f he h
    exact cover1681 f he ((@Law1681.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1681_not_termStructuralFromFin_Equation626_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1681_bits._native.bv_decide.ax_1_7] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1681_not_termStructuralFromFin_Equation626_unaryTail

