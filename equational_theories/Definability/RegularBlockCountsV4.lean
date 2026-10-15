import equational_theories.Definability.RegularBlockCounting

/-! Local unary-law counts for the regular V4 action.
Only functions on the small group are enumerated; the amplification to arbitrary
numbers of blocks is the symbolic theorem in `RegularBlockCounting`. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

open Law Law.MagmaLaw
namespace RegularBlockCounting.V4

abbrev H := Multiplicative (ZMod 2 × ZMod 2)

theorem count8 : localCount (H := H) Law8 = 112 := by decide +kernel

theorem count47 : localCount (H := H) Law47 = 88 := by decide +kernel

theorem count99 : localCount (H := H) Law99 = 136 := by decide +kernel

theorem count151 : localCount (H := H) Law151 = 256 := by decide +kernel

theorem count411 : localCount (H := H) Law411 = 118 := by decide +kernel

theorem count614 : localCount (H := H) Law614 = 70 := by decide +kernel

theorem count817 : localCount (H := H) Law817 = 64 := by decide +kernel

theorem count1020 : localCount (H := H) Law1020 = 142 := by decide +kernel

theorem count1223 : localCount (H := H) Law1223 = 142 := by decide +kernel

theorem count1629 : localCount (H := H) Law1629 = 184 := by decide +kernel

theorem count3456 : localCount (H := H) Law3456 = 136 := by decide +kernel

theorem count4380 : localCount (H := H) Law4380 = 64 := by decide +kernel

end RegularBlockCounting.V4
