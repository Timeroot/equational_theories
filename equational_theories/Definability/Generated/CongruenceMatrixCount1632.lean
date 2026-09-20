import equational_theories.Definability.CongruenceMatrixFastTest

open Law Law.MagmaLaw Magma.CongruenceMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Magma.CongruenceMatrixCounts

def law1632 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 1)))⟩
theorem count1632 : Fintype.card {p : Params // Test law1632 p} = 3564 := by native_decide

end Magma.CongruenceMatrixCounts
