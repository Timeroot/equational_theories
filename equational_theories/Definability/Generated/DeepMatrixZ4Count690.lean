import equational_theories.Definability.MatrixFamilyCounting

/-! A single large matrix count, compiled separately for parallel checking. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Magma.DeepMatrixZ4

def law690 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 2) (.Leaf 1)) (.Leaf 0))))⟩
theorem count690 : Fintype.card {p : P (ZMod 4) 2 // Test law690 p} = 528 := by
  native_decide

end Magma.DeepMatrixZ4
