import equational_theories.Definability.FivePointTable

/-! Generated finite endomorphism obstruction. Source tables are checked in
Lean's kernel; target-list completeness uses the standard bv_decide checker. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FivePointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Magma.UnaryTail12300

def step (x : Point) : Point := ![1, 2, 3, 0, 0] x
def stepBits (x : BitVec 3) : BitVec 3 := if x = 0 then 1 else if x = 1 then 2 else if x = 2 then 3 else if x = 3 then 0 else 0

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

def codes826 : Fin 30 → Code := ![21503633086612070760448, 21577420062906908966912, 21512856458648925536256, 21586643434943763742720, 21504786008116677607424, 21578572984411515813888, 21514009380153532383232, 21587796356448370589696, 21283418323841311904256, 21292641695878166680064, 21365278002442441958400, 21366430923947048805376, 21477115047582407884864, 21550902023877246091328, 21568196409393852743872, 21569349330898459590848, 21273041748823648834240, 21274194670328255681216, 21510550535375367208976, 21584337511670205415440, 21353748707132028855312, 21362972079168883631120, 21576267101270125608984, 21585490473306980384792, 21474809164441017679960, 21548596140735855886424, 110683575718869836809, 110683580116916347913, 10811274591160118556179, 10811274591160118560275]

def codes1632 : Fin 27 → Code := ![21503633086612070760448, 21577420062906908966912, 21512856458648925536256, 21586643434943763742720, 21504786008116677607424, 21578572984411515813888, 21514009380153532383232, 21587796356448370589696, 16865573988766801231872, 21283418323841311904256, 21292641695878166680064, 21365278002442441958400, 21366430923947048805376, 21477115047582407884864, 21550902023877246091328, 21568196409393852743872, 21569349330898459590848, 21273041748823648834240, 21274194670328255681216, 21510550535375367208976, 21584337511670205415440, 21353748707132028855312, 21362972079168883631120, 21576267101270125608984, 21585490473306980384792, 21474809164441017679960, 21548596140735855886424]

theorem source826_injective : Function.Injective (fun i => decode (codes826 i)) := by
  decide +kernel

theorem source826_law : ∀ i, @Equation826 Point ⟨decode (codes826 i)⟩ := by
  decide +kernel

theorem source826_endo : ∀ i, Commutes step (decode (codes826 i)) := by
  decide +kernel

def test1632 (c : Code) : Prop :=
  0 = (bits c (bits c 0 0) (bits c (bits c 0 0) 0)) ∧
  0 = (bits c (bits c 0 0) (bits c (bits c 0 1) 1)) ∧
  0 = (bits c (bits c 0 0) (bits c (bits c 0 2) 2)) ∧
  0 = (bits c (bits c 0 0) (bits c (bits c 0 3) 3)) ∧
  0 = (bits c (bits c 0 0) (bits c (bits c 0 4) 4)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 0) 0)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 1) 1)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 2) 2)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 3) 3)) ∧
  1 = (bits c (bits c 1 1) (bits c (bits c 1 4) 4)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 0) 0)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 1) 1)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 2) 2)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 3) 3)) ∧
  2 = (bits c (bits c 2 2) (bits c (bits c 2 4) 4)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 0) 0)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 1) 1)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 2) 2)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 3) 3)) ∧
  3 = (bits c (bits c 3 3) (bits c (bits c 3 4) 4)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 0) 0)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 1) 1)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 2) 2)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 3) 3)) ∧
  4 = (bits c (bits c 4 4) (bits c (bits c 4 4) 4))

theorem test1632_encode (f : Point → Point → Point) (h : @Equation1632 Point ⟨f⟩) :
    test1632 (encode f) := by
  have hh (x y : Point) :
    (point x) = (bits (encode f) (bits (encode f) (point x) (point x)) (bits (encode f) (bits (encode f) (point x) (point y)) (point y))) := by
    simp only [bits_encode]
    exact congrArg point (h x y)
  exact ⟨hh 0 0, hh 0 1, hh 0 2, hh 0 3, hh 0 4, hh 1 0, hh 1 1, hh 1 2, hh 1 3, hh 1 4, hh 2 0, hh 2 1, hh 2 2, hh 2 3, hh 2 4, hh 3 0, hh 3 1, hh 3 2, hh 3 3, hh 3 4, hh 4 0, hh 4 1, hh 4 2, hh 4 3, hh 4 4⟩

theorem cover1632_bits (c : Code) (hv : Valid c) (he : endoTest c) (h : test1632 c) :
    ∃ i, codes1632 i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero]
  change 21503633086612070760448 = c ∨ 21577420062906908966912 = c ∨ 21512856458648925536256 = c ∨ 21586643434943763742720 = c ∨ 21504786008116677607424 = c ∨ 21578572984411515813888 = c ∨ 21514009380153532383232 = c ∨ 21587796356448370589696 = c ∨ 16865573988766801231872 = c ∨ 21283418323841311904256 = c ∨ 21292641695878166680064 = c ∨ 21365278002442441958400 = c ∨ 21366430923947048805376 = c ∨ 21477115047582407884864 = c ∨ 21550902023877246091328 = c ∨ 21568196409393852743872 = c ∨ 21569349330898459590848 = c ∨ 21273041748823648834240 = c ∨ 21274194670328255681216 = c ∨ 21510550535375367208976 = c ∨ 21584337511670205415440 = c ∨ 21353748707132028855312 = c ∨ 21362972079168883631120 = c ∨ 21576267101270125608984 = c ∨ 21585490473306980384792 = c ∨ 21474809164441017679960 = c ∨ 21548596140735855886424 = c ∨ False
  unfold Valid endoTest test1632 bits stepBits at *
  bv_decide (config := { timeout := 60 })

theorem cover1632 (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation1632 Point ⟨f⟩) : ∃ i, decode (codes1632 i) = f := by
  obtain ⟨i, hi⟩ := cover1632_bits (encode f) (valid_encode f)
    (endoTest_encode f he) (test1632_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

end Magma.UnaryTail12300

open Magma.UnaryTail12300

theorem Equation1632_not_termStructuralFromFin_Equation826_unaryTail : ¬ Law1632.TermStructuralFromFin Law826 := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes826 i))
    (fun i => decode (codes1632 i)) source826_injective
  · intro i
    exact (@Law826.models_iff Point ⟨decode (codes826 i)⟩).mpr (source826_law i)
  · exact source826_endo
  · intro f he h
    exact cover1632 f he ((@Law1632.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: 'Equation1632_not_termStructuralFromFin_Equation826_unaryTail' depends on axioms: [propext, Classical.choice, Quot.sound,
cover1632_bits._native.bv_decide.ax_1_7] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1632_not_termStructuralFromFin_Equation826_unaryTail

