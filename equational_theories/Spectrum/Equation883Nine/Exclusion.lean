import equational_theories.Spectrum.Equation883Nine.CanonicalModels
import equational_theories.Spectrum.Equation883Nine.Models
import equational_theories.Spectrum.Equation883Nine.Cases.Row00
import equational_theories.Spectrum.Equation883Nine.Cases.Row01
import equational_theories.Spectrum.Equation883Nine.Cases.Row02
import equational_theories.Spectrum.Equation883Nine.Cases.Row03
import equational_theories.Spectrum.Equation883Nine.Cases.Row04
import equational_theories.Spectrum.Equation883Nine.Cases.Row05
import equational_theories.Spectrum.Equation883Nine.Cases.Row06
import equational_theories.Spectrum.Equation883Nine.Cases.Row07
import equational_theories.Spectrum.Equation883Nine.Cases.Row08
import equational_theories.Spectrum.Equation883Nine.Cases.Row09
import equational_theories.Spectrum.Equation883Nine.Cases.Row10
import equational_theories.Spectrum.Equation883Nine.Cases.Row11
import equational_theories.Spectrum.Equation883Nine.Cases.Row12
import equational_theories.Spectrum.Equation883Nine.Cases.Row13
import equational_theories.Spectrum.Equation883Nine.Cases.Row14
import equational_theories.Spectrum.Equation883Nine.Cases.Row15
import equational_theories.Spectrum.Equation883Nine.Cases.Row16
import equational_theories.Spectrum.Equation883Nine.Cases.Row17
import equational_theories.Spectrum.Equation883Nine.Cases.Row18
import equational_theories.Spectrum.Equation883Nine.Cases.Row19
import equational_theories.Spectrum.Equation883Nine.Cases.Row20
import equational_theories.Spectrum.Equation883Nine.Cases.Row22
import equational_theories.Spectrum.Equation883Nine.Cases.Row23
import equational_theories.Spectrum.Equation883Nine.Cases.Row24
import equational_theories.Spectrum.Equation883Nine.Cases.Row25
import equational_theories.Spectrum.Equation883Nine.Cases.Row26
import equational_theories.Spectrum.Equation883Nine.Cases.Row27
import equational_theories.Spectrum.Equation883Nine.Cases.Row28
import equational_theories.Spectrum.Equation883Nine.Cases.Row29
import equational_theories.Spectrum.Equation883Nine.Cases.Row30
import equational_theories.Spectrum.Equation883Nine.Cases.Row31
import equational_theories.Spectrum.Equation883Nine.Cases.Row32
import equational_theories.Spectrum.Equation883Nine.Cases.Row33
import equational_theories.Spectrum.Equation883Nine.Cases.Row34
import equational_theories.Spectrum.Equation883Nine.Cases.Row35
import equational_theories.Spectrum.Equation883Nine.Cases.Row36
import equational_theories.Spectrum.Equation883Nine.Cases.Row37
import equational_theories.Spectrum.Equation883Nine.Cases.Row38
import equational_theories.Spectrum.Equation883Nine.Cases.Row39
import equational_theories.Spectrum.Equation883Nine.Cases.Row40
import equational_theories.Spectrum.Equation883Nine.Cases.Row41
import equational_theories.Spectrum.Equation883Nine.Cases.Row42
import equational_theories.Spectrum.Equation883Nine.Cases.Row43
import equational_theories.Spectrum.Equation883Nine.Cases.Row44
import equational_theories.Spectrum.Equation883Nine.Cases.Row45
import equational_theories.Spectrum.Equation883Nine.Cases.Row46
import equational_theories.Spectrum.Equation883Nine.Cases.Row47
import equational_theories.Spectrum.Equation883Nine.Cases.Row48
import equational_theories.Spectrum.Equation883Nine.Cases.Row49
import equational_theories.Spectrum.Equation883Nine.Cases.Row50
import equational_theories.Spectrum.Equation883Nine.Cases.Row51
import equational_theories.Spectrum.Equation883Nine.Cases.Row52
import equational_theories.Spectrum.Equation883Nine.Cases.Row53
import equational_theories.Spectrum.Equation883Nine.Cases.Row54
import equational_theories.Spectrum.Equation883Nine.Cases.Row55
import equational_theories.Spectrum.Equation883Nine.Cases.Row56
import equational_theories.Spectrum.Equation883Nine.Cases.Row57
import equational_theories.Spectrum.Equation883Nine.Cases.Row58
import equational_theories.Spectrum.Equation883Nine.Cases.Row59
import equational_theories.Spectrum.Equation883Nine.Cases.Row60
import equational_theories.Spectrum.Equation883Nine.Cases.Row61
import equational_theories.Spectrum.Equation883Nine.Cases.Row62
import equational_theories.Spectrum.Equation883Nine.Cases.Row63
import equational_theories.Spectrum.Equation883Nine.Cases.Row64
import equational_theories.Spectrum.Equation883Nine.Cases.Row65
import equational_theories.Spectrum.Equation883Nine.Cases.Row66

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Spectrum.E883Nine

def rowBits (r : Fin 9 → Fin 9) : BitVec 36 := pack (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8)

theorem refuteRows (r : Fin 9 → Fin 9) (hr : r ∈ Canonical.rows)
    (hn : ∃ x, r x ≠ x) (b c d e f g h i : BitVec 36)
    (hl : testLatin (rowBits r) b c d e f g h i) :
    ¬ testLaw (rowBits r) b c d e f g h i := by
  simp only [Canonical.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact refuteRow00 b c d e f g h i hl
  · exact refuteRow01 b c d e f g h i hl
  · exact refuteRow02 b c d e f g h i hl
  · exact refuteRow03 b c d e f g h i hl
  · exact refuteRow04 b c d e f g h i hl
  · exact refuteRow05 b c d e f g h i hl
  · exact refuteRow06 b c d e f g h i hl
  · exact refuteRow07 b c d e f g h i hl
  · exact refuteRow08 b c d e f g h i hl
  · exact refuteRow09 b c d e f g h i hl
  · exact refuteRow10 b c d e f g h i hl
  · exact refuteRow11 b c d e f g h i hl
  · exact refuteRow12 b c d e f g h i hl
  · exact refuteRow13 b c d e f g h i hl
  · exact refuteRow14 b c d e f g h i hl
  · exact refuteRow15 b c d e f g h i hl
  · exact refuteRow16 b c d e f g h i hl
  · exact refuteRow17 b c d e f g h i hl
  · exact refuteRow18 b c d e f g h i hl
  · exact refuteRow19 b c d e f g h i hl
  · exact refuteRow20 b c d e f g h i hl
  · obtain ⟨x,hx⟩ := hn
    fin_cases x <;> exact False.elim (hx rfl)
  · exact refuteRow22 b c d e f g h i hl
  · exact refuteRow23 b c d e f g h i hl
  · exact refuteRow24 b c d e f g h i hl
  · exact refuteRow25 b c d e f g h i hl
  · exact refuteRow26 b c d e f g h i hl
  · exact refuteRow27 b c d e f g h i hl
  · exact refuteRow28 b c d e f g h i hl
  · exact refuteRow29 b c d e f g h i hl
  · exact refuteRow30 b c d e f g h i hl
  · exact refuteRow31 b c d e f g h i hl
  · exact refuteRow32 b c d e f g h i hl
  · exact refuteRow33 b c d e f g h i hl
  · exact refuteRow34 b c d e f g h i hl
  · exact refuteRow35 b c d e f g h i hl
  · exact refuteRow36 b c d e f g h i hl
  · exact refuteRow37 b c d e f g h i hl
  · exact refuteRow38 b c d e f g h i hl
  · exact refuteRow39 b c d e f g h i hl
  · exact refuteRow40 b c d e f g h i hl
  · exact refuteRow41 b c d e f g h i hl
  · exact refuteRow42 b c d e f g h i hl
  · exact refuteRow43 b c d e f g h i hl
  · exact refuteRow44 b c d e f g h i hl
  · exact refuteRow45 b c d e f g h i hl
  · exact refuteRow46 b c d e f g h i hl
  · exact refuteRow47 b c d e f g h i hl
  · exact refuteRow48 b c d e f g h i hl
  · exact refuteRow49 b c d e f g h i hl
  · exact refuteRow50 b c d e f g h i hl
  · exact refuteRow51 b c d e f g h i hl
  · exact refuteRow52 b c d e f g h i hl
  · exact refuteRow53 b c d e f g h i hl
  · exact refuteRow54 b c d e f g h i hl
  · exact refuteRow55 b c d e f g h i hl
  · exact refuteRow56 b c d e f g h i hl
  · exact refuteRow57 b c d e f g h i hl
  · exact refuteRow58 b c d e f g h i hl
  · exact refuteRow59 b c d e f g h i hl
  · exact refuteRow60 b c d e f g h i hl
  · exact refuteRow61 b c d e f g h i hl
  · exact refuteRow62 b c d e f g h i hl
  · exact refuteRow63 b c d e f g h i hl
  · exact refuteRow64 b c d e f g h i hl
  · exact refuteRow65 b c d e f g h i hl
  · exact refuteRow66 b c d e f g h i hl

theorem not_order_883_9 : ¬ Law883.HasModel 9 := by
  intro h
  obtain ⟨M,hM,r,hr,hrow,hn⟩ := canonical_model h
  have hbits : rows M 0 = rowBits r := by
    simp only [rows, rowBits, hrow]
  have hLatin := modelLatin M hM
  have hLaw := modelLaw M hM
  rw [hbits] at hLatin hLaw
  exact refuteRows r hr hn (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6) (rows M 7) (rows M 8) hLatin hLaw
spectrum_assert not_order_883_9 complete

end Spectrum.E883Nine
