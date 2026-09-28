import equational_theories.Definability.Cyclic1483.Bridge
import equational_theories.Definability.Cyclic1483.FiniteCertificate

/-! An eight-element cyclic NAND model separates E1483 from E1485 for finite
first-order structural recovery. -/

namespace Definability.Cyclic1483

open Spectrum.FiniteTableEncoding.N8
open Law Law.MagmaLaw

theorem enlarged_symmetry (M : Magma (Fin 8))
    (hr : M.IsEndo rotateEquiv) (hm : @Equation1485 (Fin 8) M) :
    M.IsEndo reflectEquiv0 ∨ M.IsEndo reflectEquiv1 ∨ M.IsEndo reflectEquiv2 := by
  have h := FiniteCertificate.certificate
    (rows M 0) (rows M 1) (rows M 2) (rows M 3)
    (rows M 4) (rows M 5) (rows M 6) (rows M 7)
    (rotationTest_of M hr) (lawTest_of M hm)
  rcases h with h | h | h
  · exact Or.inl (reflectionTest0_to M h)
  · exact Or.inr (Or.inl (reflectionTest1_to M h))
  · exact Or.inr (Or.inr (reflectionTest2_to M h))

theorem Equation1485_not_structuralFromFin_Equation1483 :
    ¬ Law1485.StructuralFromFin Law1483 := by
  intro h
  obtain ⟨M, hM, hforward, hback⟩ := h source
    ((@Law1483.models_iff (Fin 8) source).mpr source_models)
  have hr : M.IsEndo rotateEquiv :=
    Magma.IsEndo.of_definable hforward source_rotation
  rcases enlarged_symmetry M hr ((@Law1485.models_iff (Fin 8) M).mp hM) with h | h | h
  · exact source_not_reflection0 (Magma.IsEndo.of_definable hback h)
  · exact source_not_reflection1 (Magma.IsEndo.of_definable hback h)
  · exact source_not_reflection2 (Magma.IsEndo.of_definable hback h)

/-- info: 'Definability.Cyclic1483.Equation1485_not_structuralFromFin_Equation1483' depends on axioms: [propext, Classical.choice, Quot.sound, FiniteCertificate.certificate._native.bv_decide.ax_1_5] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1485_not_structuralFromFin_Equation1483
end Definability.Cyclic1483
