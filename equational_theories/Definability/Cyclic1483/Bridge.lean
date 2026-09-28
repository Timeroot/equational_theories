import equational_theories.Definability.Cyclic1483.Base
import equational_theories.Definability.Cyclic1483.FiniteEncoding

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace Definability.Cyclic1483
open Spectrum.FiniteTableEncoding.N8 FiniteCertificate

theorem bv_rotate (x : Fin 8) : rotation (bv x) = bv (rotate x) := by
  fin_cases x <;> decide +kernel

theorem bv_reflect0 (x : Fin 8) : reflection0 (bv x) = bv (reflect0 x) := by
  fin_cases x <;> decide +kernel

theorem bv_reflect1 (x : Fin 8) : reflection1 (bv x) = bv (reflect1 x) := by
  fin_cases x <;> decide +kernel

theorem bv_reflect2 (x : Fin 8) : reflection2 (bv x) = bv (reflect2 x) := by
  fin_cases x <;> decide +kernel

theorem rotationTest_of (M : Magma (Fin 8)) (hr : M.IsEndo rotateEquiv) :
    rotationTest (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6) (rows M 7) := by
  have H (x y : Fin 8) : rotation (encoded M (bv x) (bv y)) =
      encoded M (bv (rotate x)) (bv (rotate y)) := by
    rw [encoded_eq, encoded_eq, bv_rotate]
    exact congrArg bv (hr x y)
  exact ⟨H 0 0, H 0 1, H 0 2, H 0 3, H 0 4, H 0 5, H 0 6, H 0 7, H 1 0, H 1 1, H 1 2, H 1 3, H 1 4, H 1 5, H 1 6, H 1 7, H 2 0, H 2 1, H 2 2, H 2 3, H 2 4, H 2 5, H 2 6, H 2 7, H 3 0, H 3 1, H 3 2, H 3 3, H 3 4, H 3 5, H 3 6, H 3 7, H 4 0, H 4 1, H 4 2, H 4 3, H 4 4, H 4 5, H 4 6, H 4 7, H 5 0, H 5 1, H 5 2, H 5 3, H 5 4, H 5 5, H 5 6, H 5 7, H 6 0, H 6 1, H 6 2, H 6 3, H 6 4, H 6 5, H 6 6, H 6 7, H 7 0, H 7 1, H 7 2, H 7 3, H 7 4, H 7 5, H 7 6, H 7 7⟩

theorem lawTest_of (M : Magma (Fin 8)) (hm : @Equation1485 (Fin 8) M) :
    lawTest (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6) (rows M 7) := by
  have H (x y z : Fin 8) : bv x = encoded M (encoded M (bv y) (bv x))
      (encoded M (bv x) (encoded M (bv z) (bv y))) := by
    simp only [encoded_eq]
    exact congrArg bv (hm x y z)
  exact ⟨H 0 0 0, H 0 0 1, H 0 0 3, H 0 0 7, H 0 1 0, H 0 1 1, H 0 1 2, H 0 1 3, H 0 1 4, H 0 1 5, H 0 1 6, H 0 1 7, H 0 3 0, H 0 3 1, H 0 3 2, H 0 3 3, H 0 3 4, H 0 3 5, H 0 3 6, H 0 3 7, H 0 7 0, H 0 7 1, H 0 7 3, H 0 7 7, H 1 0 0, H 1 0 1, H 1 0 2, H 1 0 3, H 1 0 4, H 1 0 5, H 1 0 6, H 1 0 7, H 1 1 0, H 1 1 1, H 1 1 2, H 1 1 3, H 1 1 4, H 1 1 5, H 1 1 6, H 1 1 7, H 1 2 0, H 1 2 1, H 1 2 2, H 1 2 3, H 1 2 4, H 1 2 5, H 1 2 6, H 1 2 7, H 1 3 0, H 1 3 1, H 1 3 2, H 1 3 3, H 1 3 4, H 1 3 5, H 1 3 6, H 1 3 7, H 1 4 0, H 1 4 1, H 1 4 2, H 1 4 3, H 1 4 4, H 1 4 5, H 1 4 6, H 1 4 7, H 1 5 0, H 1 5 1, H 1 5 2, H 1 5 3, H 1 5 4, H 1 5 5, H 1 5 6, H 1 5 7, H 1 6 0, H 1 6 1, H 1 6 2, H 1 6 3, H 1 6 4, H 1 6 5, H 1 6 6, H 1 6 7, H 1 7 0, H 1 7 1, H 1 7 2, H 1 7 3, H 1 7 4, H 1 7 5, H 1 7 6, H 1 7 7, H 3 0 0, H 3 0 1, H 3 0 2, H 3 0 3, H 3 0 4, H 3 0 5, H 3 0 6, H 3 0 7, H 3 1 0, H 3 1 1, H 3 1 2, H 3 1 3, H 3 1 4, H 3 1 5, H 3 1 6, H 3 1 7, H 3 2 0, H 3 2 1, H 3 2 2, H 3 2 3, H 3 2 4, H 3 2 5, H 3 2 6, H 3 2 7, H 3 3 0, H 3 3 1, H 3 3 2, H 3 3 3, H 3 3 4, H 3 3 5, H 3 3 6, H 3 3 7, H 3 4 0, H 3 4 1, H 3 4 2, H 3 4 3, H 3 4 4, H 3 4 5, H 3 4 6, H 3 4 7, H 3 5 0, H 3 5 1, H 3 5 2, H 3 5 3, H 3 5 4, H 3 5 5, H 3 5 6, H 3 5 7, H 3 6 0, H 3 6 1, H 3 6 2, H 3 6 3, H 3 6 4, H 3 6 5, H 3 6 6, H 3 6 7, H 3 7 0, H 3 7 1, H 3 7 2, H 3 7 3, H 3 7 4, H 3 7 5, H 3 7 6, H 3 7 7, H 7 0 0, H 7 0 1, H 7 0 3, H 7 0 7, H 7 1 0, H 7 1 1, H 7 1 2, H 7 1 3, H 7 1 4, H 7 1 5, H 7 1 6, H 7 1 7, H 7 3 0, H 7 3 1, H 7 3 2, H 7 3 3, H 7 3 4, H 7 3 5, H 7 3 6, H 7 3 7, H 7 7 0, H 7 7 1, H 7 7 3, H 7 7 7⟩

theorem reflectionTest0_to (M : Magma (Fin 8))
    (h : reflectionTest0 (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6) (rows M 7)) : M.IsEndo reflectEquiv0 := by
  have H (x y : Fin 8) : reflection0 (encoded M (bv x) (bv y)) =
      encoded M (bv (reflect0 x)) (bv (reflect0 y)) := by
    rcases h with ⟨h00, h01, h02, h03, h04, h05, h06, h07, h10, h11, h12, h13, h14, h15, h16, h17, h20, h21, h22, h23, h24, h25, h26, h27, h30, h31, h32, h33, h34, h35, h36, h37, h40, h41, h42, h43, h44, h45, h46, h47, h50, h51, h52, h53, h54, h55, h56, h57, h60, h61, h62, h63, h64, h65, h66, h67, h70, h71, h72, h73, h74, h75, h76, h77⟩
    fin_cases x <;> fin_cases y <;> assumption
  intro x y
  apply bv_injective
  change bv (reflect0 (M.op x y)) = bv (M.op (reflect0 x) (reflect0 y))
  rw [← bv_reflect0, ← encoded_eq, ← encoded_eq]
  exact H x y

theorem reflectionTest1_to (M : Magma (Fin 8))
    (h : reflectionTest1 (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6) (rows M 7)) : M.IsEndo reflectEquiv1 := by
  have H (x y : Fin 8) : reflection1 (encoded M (bv x) (bv y)) =
      encoded M (bv (reflect1 x)) (bv (reflect1 y)) := by
    rcases h with ⟨h00, h01, h02, h03, h04, h05, h06, h07, h10, h11, h12, h13, h14, h15, h16, h17, h20, h21, h22, h23, h24, h25, h26, h27, h30, h31, h32, h33, h34, h35, h36, h37, h40, h41, h42, h43, h44, h45, h46, h47, h50, h51, h52, h53, h54, h55, h56, h57, h60, h61, h62, h63, h64, h65, h66, h67, h70, h71, h72, h73, h74, h75, h76, h77⟩
    fin_cases x <;> fin_cases y <;> assumption
  intro x y
  apply bv_injective
  change bv (reflect1 (M.op x y)) = bv (M.op (reflect1 x) (reflect1 y))
  rw [← bv_reflect1, ← encoded_eq, ← encoded_eq]
  exact H x y

theorem reflectionTest2_to (M : Magma (Fin 8))
    (h : reflectionTest2 (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6) (rows M 7)) : M.IsEndo reflectEquiv2 := by
  have H (x y : Fin 8) : reflection2 (encoded M (bv x) (bv y)) =
      encoded M (bv (reflect2 x)) (bv (reflect2 y)) := by
    rcases h with ⟨h00, h01, h02, h03, h04, h05, h06, h07, h10, h11, h12, h13, h14, h15, h16, h17, h20, h21, h22, h23, h24, h25, h26, h27, h30, h31, h32, h33, h34, h35, h36, h37, h40, h41, h42, h43, h44, h45, h46, h47, h50, h51, h52, h53, h54, h55, h56, h57, h60, h61, h62, h63, h64, h65, h66, h67, h70, h71, h72, h73, h74, h75, h76, h77⟩
    fin_cases x <;> fin_cases y <;> assumption
  intro x y
  apply bv_injective
  change bv (reflect2 (M.op x y)) = bv (M.op (reflect2 x) (reflect2 y))
  rw [← bv_reflect2, ← encoded_eq, ← encoded_eq]
  exact H x y

end Definability.Cyclic1483
