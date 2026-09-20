import equational_theories.Definability.CongruenceMatrixFastTest

open Law Law.MagmaLaw Magma.CongruenceMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Magma.CongruenceMatrixCounts

def law1045 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 0))) (.Leaf 0)))⟩
theorem count1045 : Fintype.card {p : Params // Test law1045 p} = 3133 := by native_decide

end Magma.CongruenceMatrixCounts
