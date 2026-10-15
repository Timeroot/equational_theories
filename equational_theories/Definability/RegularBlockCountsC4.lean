import equational_theories.Definability.RegularBlockCounting

/-! Local unary-law counts for the regular C4 action.
Only functions on the small group are enumerated; the amplification to arbitrary
numbers of blocks is the symbolic theorem in `RegularBlockCounting`. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

open Law Law.MagmaLaw
namespace RegularBlockCounting.C4

abbrev H := Multiplicative (ZMod 4)

theorem count8 : localCount (H := H) Law8 = 112 := by decide +kernel

theorem count411 : localCount (H := H) Law411 = 118 := by decide +kernel

theorem count614 : localCount (H := H) Law614 = 94 := by decide +kernel

theorem count817 : localCount (H := H) Law817 = 96 := by decide +kernel

theorem count1020 : localCount (H := H) Law1020 = 134 := by decide +kernel

theorem count1223 : localCount (H := H) Law1223 = 110 := by decide +kernel

theorem count1426 : localCount (H := H) Law1426 = 104 := by decide +kernel

theorem count4380 : localCount (H := H) Law4380 = 96 := by decide +kernel

end RegularBlockCounting.C4
