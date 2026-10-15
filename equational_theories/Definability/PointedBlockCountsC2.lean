import equational_theories.Definability.PointedBlockCounting

/-! Local counts for the C2 action with one shared fixed point. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

open Law Law.MagmaLaw
namespace PointedBlockCounting.C2

abbrev H := Multiplicative (ZMod 2)

theorem count99 : localCount (H := H) Law99 = 45 := by decide +kernel

theorem count614 : localCount (H := H) Law614 = 32 := by decide +kernel

theorem count817 : localCount (H := H) Law817 = 36 := by decide +kernel

theorem count1020 : localCount (H := H) Law1020 = 50 := by decide +kernel

theorem count1223 : localCount (H := H) Law1223 = 47 := by decide +kernel

theorem count1426 : localCount (H := H) Law1426 = 45 := by decide +kernel

theorem count3659 : localCount (H := H) Law3659 = 54 := by decide +kernel

theorem count4380 : localCount (H := H) Law4380 = 45 := by decide +kernel

end PointedBlockCounting.C2
