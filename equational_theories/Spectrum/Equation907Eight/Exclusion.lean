import equational_theories.Spectrum.Equation907Eight.CanonicalModels
import equational_theories.Spectrum.Equation907Eight.Models
import equational_theories.Spectrum.Equation907Eight.Cases.Row00
import equational_theories.Spectrum.Equation907Eight.Cases.Row01
import equational_theories.Spectrum.Equation907Eight.Cases.Row02
import equational_theories.Spectrum.Equation907Eight.Cases.Row03
import equational_theories.Spectrum.Equation907Eight.Cases.Row04
import equational_theories.Spectrum.Equation907Eight.Cases.Row05
import equational_theories.Spectrum.Equation907Eight.Cases.Row06
import equational_theories.Spectrum.Equation907Eight.Cases.Row07
import equational_theories.Spectrum.Equation907Eight.Cases.Row08
import equational_theories.Spectrum.Equation907Eight.Cases.Row09
import equational_theories.Spectrum.Equation907Eight.Cases.Row10
import equational_theories.Spectrum.Equation907Eight.Cases.Row11
import equational_theories.Spectrum.Equation907Eight.Cases.Row12
import equational_theories.Spectrum.Equation907Eight.Cases.Row13
import equational_theories.Spectrum.Equation907Eight.Cases.Row14
import equational_theories.Spectrum.Equation907Eight.Cases.Row15
import equational_theories.Spectrum.Equation907Eight.Cases.Row16
import equational_theories.Spectrum.Equation907Eight.Cases.Row17
import equational_theories.Spectrum.Equation907Eight.Cases.Row18
import equational_theories.Spectrum.Equation907Eight.Cases.Row19
import equational_theories.Spectrum.Equation907Eight.Cases.Row20
import equational_theories.Spectrum.Equation907Eight.Cases.Row21
import equational_theories.Spectrum.Equation907Eight.Cases.Row22
import equational_theories.Spectrum.Equation907Eight.Cases.Row23
import equational_theories.Spectrum.Equation907Eight.Cases.Row24
import equational_theories.Spectrum.Equation907Eight.Cases.Row25
import equational_theories.Spectrum.Equation907Eight.Cases.Row26
import equational_theories.Spectrum.Equation907Eight.Cases.Row27
import equational_theories.Spectrum.Equation907Eight.Cases.Row28
import equational_theories.Spectrum.Equation907Eight.Cases.Row29
import equational_theories.Spectrum.Equation907Eight.Cases.Row30
import equational_theories.Spectrum.Equation907Eight.Cases.Row31
import equational_theories.Spectrum.Equation907Eight.Cases.Row32
import equational_theories.Spectrum.Equation907Eight.Cases.Row33
import equational_theories.Spectrum.Equation907Eight.Cases.Row34
import equational_theories.Spectrum.Equation907Eight.Cases.Row35
import equational_theories.Spectrum.Equation907Eight.Cases.Row36
import equational_theories.Spectrum.Equation907Eight.Cases.Row37
import equational_theories.Spectrum.Equation907Eight.Cases.Row38
import equational_theories.Spectrum.Equation907Eight.Cases.Row39
import equational_theories.Spectrum.Equation907Eight.Cases.Row40
import equational_theories.Spectrum.Equation907Eight.Cases.Row41
import equational_theories.Spectrum.Equation907Eight.Cases.Row42
import equational_theories.Spectrum.Equation907Eight.Cases.Row43
import equational_theories.Spectrum.Equation907Eight.Cases.Row44

set_option maxHeartbeats 16000000
set_option maxRecDepth 32768

namespace Spectrum.E907Eight
def rowBits (r : Fin 8 → Fin 8) : BitVec 24 := pack (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7)

theorem refuteRows (r : Fin 8 → Fin 8) (hr : r ∈ Canonical.rows) (b c d e f g h : BitVec 24)
    (hl : testLatin (rowBits r) b c d e f g h) : ¬ testLaw (rowBits r) b c d e f g h := by
  simp only [Canonical.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact refuteRow00 b c d e f g h hl
  · exact refuteRow01 b c d e f g h hl
  · exact refuteRow02 b c d e f g h hl
  · exact refuteRow03 b c d e f g h hl
  · exact refuteRow04 b c d e f g h hl
  · exact refuteRow05 b c d e f g h hl
  · exact refuteRow06 b c d e f g h hl
  · exact refuteRow07 b c d e f g h hl
  · exact refuteRow08 b c d e f g h hl
  · exact refuteRow09 b c d e f g h hl
  · exact refuteRow10 b c d e f g h hl
  · exact refuteRow11 b c d e f g h hl
  · exact refuteRow12 b c d e f g h hl
  · exact refuteRow13 b c d e f g h hl
  · exact refuteRow14 b c d e f g h hl
  · exact refuteRow15 b c d e f g h hl
  · exact refuteRow16 b c d e f g h hl
  · exact refuteRow17 b c d e f g h hl
  · exact refuteRow18 b c d e f g h hl
  · exact refuteRow19 b c d e f g h hl
  · exact refuteRow20 b c d e f g h hl
  · exact refuteRow21 b c d e f g h hl
  · exact refuteRow22 b c d e f g h hl
  · exact refuteRow23 b c d e f g h hl
  · exact refuteRow24 b c d e f g h hl
  · exact refuteRow25 b c d e f g h hl
  · exact refuteRow26 b c d e f g h hl
  · exact refuteRow27 b c d e f g h hl
  · exact refuteRow28 b c d e f g h hl
  · exact refuteRow29 b c d e f g h hl
  · exact refuteRow30 b c d e f g h hl
  · exact refuteRow31 b c d e f g h hl
  · exact refuteRow32 b c d e f g h hl
  · exact refuteRow33 b c d e f g h hl
  · exact refuteRow34 b c d e f g h hl
  · exact refuteRow35 b c d e f g h hl
  · exact refuteRow36 b c d e f g h hl
  · exact refuteRow37 b c d e f g h hl
  · exact refuteRow38 b c d e f g h hl
  · exact refuteRow39 b c d e f g h hl
  · exact refuteRow40 b c d e f g h hl
  · exact refuteRow41 b c d e f g h hl
  · exact refuteRow42 b c d e f g h hl
  · exact refuteRow43 b c d e f g h hl
  · exact refuteRow44 b c d e f g h hl

theorem not_order_907_8 : ¬ Law907.HasModel 8 := by
  intro h
  obtain ⟨M,hM,r,hr,hrow⟩ := canonical_model h
  have hbits : rows M 0 = rowBits r := by
    simp only [rows, rowBits, hrow]
  have hLatin := modelLatin M hM
  have hLaw := modelLaw M hM
  rw [hbits] at hLatin hLaw
  exact refuteRows r hr (rows M 1) (rows M 2) (rows M 3) (rows M 4)
    (rows M 5) (rows M 6) (rows M 7) hLatin hLaw
spectrum_assert not_order_907_8 complete

end Spectrum.E907Eight
