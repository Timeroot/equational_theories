import equational_theories.Definability.MatrixFamilyCounting

/-! A single large matrix count, compiled separately for parallel checking. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Magma.DeepMatrixZ4

def law632 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 0))))⟩
theorem count632 : Fintype.card {p : P (ZMod 4) 2 // Test law632 p} = 409 := by
  native_decide

end Magma.DeepMatrixZ4
