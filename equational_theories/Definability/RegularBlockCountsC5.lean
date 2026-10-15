import equational_theories.Definability.RegularBlockCounting

/-! Local unary-law counts for the regular C5 action.
Only functions on the small group are enumerated; the amplification to arbitrary
numbers of blocks is the symbolic theorem in `RegularBlockCounting`. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

open Law Law.MagmaLaw
namespace RegularBlockCounting.C5

abbrev H := Multiplicative (ZMod 5)

theorem count614 : localCount (H := H) Law614 = 1045 := by decide +kernel

theorem count817 : localCount (H := H) Law817 = 1125 := by decide +kernel

theorem count1426 : localCount (H := H) Law1426 = 925 := by decide +kernel

theorem count4380 : localCount (H := H) Law4380 = 1125 := by decide +kernel

end RegularBlockCounting.C5
