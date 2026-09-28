import equational_theories.Spectrum.Equation667883Small.Basic

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Spectrum.E667883
open MendelsohnSix (bv clip)
open QuasigroupSix

def test667 (a b c d e f : BitVec 18) : Prop :=
  (0 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f (op a b c d e f 0 0) 0))) ∧
  (0 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f (op a b c d e f 0 0) 1))) ∧
  (0 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f (op a b c d e f 0 0) 2))) ∧
  (0 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f (op a b c d e f 0 0) 3))) ∧
  (0 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f (op a b c d e f 0 0) 4))) ∧
  (0 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f (op a b c d e f 0 0) 5))) ∧
  (1 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f (op a b c d e f 1 1) 0))) ∧
  (1 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f (op a b c d e f 1 1) 1))) ∧
  (1 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f (op a b c d e f 1 1) 2))) ∧
  (1 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f (op a b c d e f 1 1) 3))) ∧
  (1 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f (op a b c d e f 1 1) 4))) ∧
  (1 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f (op a b c d e f 1 1) 5))) ∧
  (2 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f (op a b c d e f 2 2) 0))) ∧
  (2 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f (op a b c d e f 2 2) 1))) ∧
  (2 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f (op a b c d e f 2 2) 2))) ∧
  (2 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f (op a b c d e f 2 2) 3))) ∧
  (2 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f (op a b c d e f 2 2) 4))) ∧
  (2 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f (op a b c d e f 2 2) 5))) ∧
  (3 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f (op a b c d e f 3 3) 0))) ∧
  (3 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f (op a b c d e f 3 3) 1))) ∧
  (3 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f (op a b c d e f 3 3) 2))) ∧
  (3 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f (op a b c d e f 3 3) 3))) ∧
  (3 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f (op a b c d e f 3 3) 4))) ∧
  (3 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f (op a b c d e f 3 3) 5))) ∧
  (4 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f (op a b c d e f 4 4) 0))) ∧
  (4 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f (op a b c d e f 4 4) 1))) ∧
  (4 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f (op a b c d e f 4 4) 2))) ∧
  (4 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f (op a b c d e f 4 4) 3))) ∧
  (4 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f (op a b c d e f 4 4) 4))) ∧
  (4 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f (op a b c d e f 4 4) 5))) ∧
  (5 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f (op a b c d e f 5 5) 0))) ∧
  (5 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f (op a b c d e f 5 5) 1))) ∧
  (5 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f (op a b c d e f 5 5) 2))) ∧
  (5 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f (op a b c d e f 5 5) 3))) ∧
  (5 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f (op a b c d e f 5 5) 4))) ∧
  (5 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f (op a b c d e f 5 5) 5)))

@[spectrum_native]
theorem refute667 (a b c d e f : BitVec 18) : ¬ test667 a b c d e f := by
  unfold test667 QuasigroupSix.op clip
  bv_decide (config := { timeout := 90, embeddedConstraintSubst := false })
spectrum_assert refute667 complete

theorem impossible667 (M : Magma (Fin 6)) (h : @Equation667 (Fin 6) M) : False := by
  have he := QuasigroupSix.encoded_eq M
  have H (x y : Fin 6) : bv x = (QuasigroupSix.encoded M (bv y) (QuasigroupSix.encoded M (bv x) (QuasigroupSix.encoded M (QuasigroupSix.encoded M (bv x) (bv x)) (bv y)))) := by
    simp only [he]
    exact congrArg bv (h x y)
  apply refute667 (QuasigroupSix.rows M 0) (QuasigroupSix.rows M 1) (QuasigroupSix.rows M 2)
    (QuasigroupSix.rows M 3) (QuasigroupSix.rows M 4) (QuasigroupSix.rows M 5)
  exact ⟨H 0 0, H 0 1, H 0 2, H 0 3, H 0 4, H 0 5, H 1 0, H 1 1, H 1 2, H 1 3, H 1 4, H 1 5, H 2 0, H 2 1, H 2 2, H 2 3, H 2 4, H 2 5, H 3 0, H 3 1, H 3 2, H 3 3, H 3 4, H 3 5, H 4 0, H 4 1, H 4 2, H 4 3, H 4 4, H 4 5, H 5 0, H 5 1, H 5 2, H 5 3, H 5 4, H 5 5⟩

theorem not_order_667_6 : ¬ Law667.HasModel 6 := by
  rintro ⟨M,hM⟩
  exact impossible667 M ((@Law667.models_iff _ M).mp hM)
spectrum_assert not_order_667_6 complete

end Spectrum.E667883
