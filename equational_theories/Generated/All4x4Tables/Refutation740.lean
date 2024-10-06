
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,3,4,5,6,7,8,9,10,11,12,1],[2,1,11,7,9,4,8,0,3,12,6,5,10],[3,11,2,12,8,10,5,9,0,4,1,7,6],[4,7,12,3,1,9,11,6,10,0,5,2,8],[5,9,8,1,4,2,10,12,7,11,0,6,3],[6,4,10,9,2,5,3,11,1,8,12,0,7],[7,8,5,11,10,3,6,4,12,2,9,1,0],[8,0,9,6,12,11,4,7,5,1,3,10,2],[9,3,0,10,7,1,12,5,8,6,2,4,11],[10,12,4,0,11,8,2,1,6,9,7,3,5],[11,6,1,5,0,12,9,3,2,7,10,8,4],[12,5,7,2,6,0,1,10,4,3,8,11,9],[1,10,6,8,3,7,0,2,11,5,4,9,12]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,3,4,5,6,7,8,9,10,11,12,1],[2,1,11,7,9,4,8,0,3,12,6,5,10],[3,11,2,12,8,10,5,9,0,4,1,7,6],[4,7,12,3,1,9,11,6,10,0,5,2,8],[5,9,8,1,4,2,10,12,7,11,0,6,3],[6,4,10,9,2,5,3,11,1,8,12,0,7],[7,8,5,11,10,3,6,4,12,2,9,1,0],[8,0,9,6,12,11,4,7,5,1,3,10,2],[9,3,0,10,7,1,12,5,8,6,2,4,11],[10,12,4,0,11,8,2,1,6,9,7,3,5],[11,6,1,5,0,12,9,3,2,7,10,8,4],[12,5,7,2,6,0,1,10,4,3,8,11,9],[1,10,6,8,3,7,0,2,11,5,4,9,12]]» : Magma (Fin 13) where
  op := memoFinOp fun x y => [[0,2,3,4,5,6,7,8,9,10,11,12,1],[2,1,11,7,9,4,8,0,3,12,6,5,10],[3,11,2,12,8,10,5,9,0,4,1,7,6],[4,7,12,3,1,9,11,6,10,0,5,2,8],[5,9,8,1,4,2,10,12,7,11,0,6,3],[6,4,10,9,2,5,3,11,1,8,12,0,7],[7,8,5,11,10,3,6,4,12,2,9,1,0],[8,0,9,6,12,11,4,7,5,1,3,10,2],[9,3,0,10,7,1,12,5,8,6,2,4,11],[10,12,4,0,11,8,2,1,6,9,7,3,5],[11,6,1,5,0,12,9,3,2,7,10,8,4],[12,5,7,2,6,0,1,10,4,3,8,11,9],[1,10,6,8,3,7,0,2,11,5,4,9,12]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,3,4,5,6,7,8,9,10,11,12,1],[2,1,11,7,9,4,8,0,3,12,6,5,10],[3,11,2,12,8,10,5,9,0,4,1,7,6],[4,7,12,3,1,9,11,6,10,0,5,2,8],[5,9,8,1,4,2,10,12,7,11,0,6,3],[6,4,10,9,2,5,3,11,1,8,12,0,7],[7,8,5,11,10,3,6,4,12,2,9,1,0],[8,0,9,6,12,11,4,7,5,1,3,10,2],[9,3,0,10,7,1,12,5,8,6,2,4,11],[10,12,4,0,11,8,2,1,6,9,7,3,5],[11,6,1,5,0,12,9,3,2,7,10,8,4],[12,5,7,2,6,0,1,10,4,3,8,11,9],[1,10,6,8,3,7,0,2,11,5,4,9,12]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1076, 2531] [55, 65, 73, 118, 127, 160, 167, 209, 229, 261, 263, 274, 419, 429, 436, 437, 464, 466, 473, 474, 504, 513, 617, 632, 633, 640, 642, 669, 677, 679, 704, 826, 833, 845, 872, 879, 883, 917, 1026, 1029, 1039, 1045, 1046, 1075, 1085, 1086, 1110, 1119, 1122, 1226, 1229, 1231, 1242, 1278, 1279, 1434, 1444, 1482, 1491, 1518, 1525, 1526, 1632, 1654, 1655, 1658, 1682, 1691, 1721, 1722, 1731, 1838, 1840, 1851, 1861, 1885, 1897, 1921, 1925, 2044, 2053, 2054, 2060, 2061, 2100, 2101, 2125, 2137, 2254, 2263, 2267, 2300, 2327, 2328, 2330, 2449, 2450, 2457, 2467, 2497, 2503, 2506, 2533, 2540, 2541, 2650, 2660, 2672, 2699, 2710, 2743, 2744, 2863, 2865, 2873, 2875, 2903, 2910, 2912, 2936, 2939, 3056, 3058, 3066, 3068, 3075, 3079, 3103, 3113, 3115, 3143, 3261, 3271, 3278, 3279, 3306, 3343, 3345, 3352, 3353, 3459, 3474, 3475, 3482, 3484, 3518, 3548, 3556, 3558, 3668, 3675, 3687, 3748, 3761, 3868, 3871, 3881, 3887, 3888, 3924, 3951, 3954, 3962, 4068, 4071, 4073, 4084, 4127, 4130, 4131, 4157, 4164, 4275, 4290, 4321, 4408, 4443, 4479, 4605, 4636, 4656] :=
    ⟨Fin 13, «FinitePoly [[0,2,3,4,5,6,7,8,9,10,11,12,1],[2,1,11,7,9,4,8,0,3,12,6,5,10],[3,11,2,12,8,10,5,9,0,4,1,7,6],[4,7,12,3,1,9,11,6,10,0,5,2,8],[5,9,8,1,4,2,10,12,7,11,0,6,3],[6,4,10,9,2,5,3,11,1,8,12,0,7],[7,8,5,11,10,3,6,4,12,2,9,1,0],[8,0,9,6,12,11,4,7,5,1,3,10,2],[9,3,0,10,7,1,12,5,8,6,2,4,11],[10,12,4,0,11,8,2,1,6,9,7,3,5],[11,6,1,5,0,12,9,3,2,7,10,8,4],[12,5,7,2,6,0,1,10,4,3,8,11,9],[1,10,6,8,3,7,0,2,11,5,4,9,12]]», by decideFin!⟩