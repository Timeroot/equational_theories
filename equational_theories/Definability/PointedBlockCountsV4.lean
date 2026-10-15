import equational_theories.Definability.PointedBlockCounting

/-! Local counts for the V4 action with one shared fixed point. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

open Law Law.MagmaLaw
namespace PointedBlockCounting.V4

abbrev H := Multiplicative (ZMod 2 × ZMod 2)

theorem count1629 : localCount (H := H) Law1629 = 10500 := by decide +kernel

theorem count3253 : localCount (H := H) Law3253 = 9625 := by decide +kernel

end PointedBlockCounting.V4
