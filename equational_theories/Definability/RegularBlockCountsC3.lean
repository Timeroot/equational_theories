import equational_theories.Definability.RegularBlockCounting

/-! Local unary-law counts for the regular C3 action.
Only functions on the small group are enumerated; the amplification to arbitrary
numbers of blocks is the symbolic theorem in `RegularBlockCounting`. -/

open Law Law.MagmaLaw
namespace RegularBlockCounting.C3

abbrev H := Multiplicative (ZMod 3)

theorem count3 : localCount (H := H) Law3 = 9 := by decide +kernel

theorem count8 : localCount (H := H) Law8 = 15 := by decide +kernel

theorem count47 : localCount (H := H) Law47 = 11 := by decide +kernel

theorem count99 : localCount (H := H) Law99 = 11 := by decide +kernel

theorem count151 : localCount (H := H) Law151 = 9 := by decide +kernel

theorem count411 : localCount (H := H) Law411 = 15 := by decide +kernel

theorem count614 : localCount (H := H) Law614 = 15 := by decide +kernel

theorem count817 : localCount (H := H) Law817 = 15 := by decide +kernel

theorem count1020 : localCount (H := H) Law1020 = 15 := by decide +kernel

theorem count1223 : localCount (H := H) Law1223 = 13 := by decide +kernel

theorem count1426 : localCount (H := H) Law1426 = 17 := by decide +kernel

theorem count1629 : localCount (H := H) Law1629 = 17 := by decide +kernel

theorem count3253 : localCount (H := H) Law3253 = 23 := by decide +kernel

theorem count3456 : localCount (H := H) Law3456 = 23 := by decide +kernel

theorem count3659 : localCount (H := H) Law3659 = 9 := by decide +kernel

theorem count4380 : localCount (H := H) Law4380 = 15 := by decide +kernel

end RegularBlockCounting.C3
