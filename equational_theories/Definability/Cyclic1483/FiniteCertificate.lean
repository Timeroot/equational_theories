import equational_theories.Definability.Cyclic1483.FiniteEncoding

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace Definability.Cyclic1483.FiniteCertificate
open Spectrum.FiniteTableEncoding.N8

@[spectrum_native]
theorem certificate (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 24) :
    rotationTest a0 a1 a2 a3 a4 a5 a6 a7 → lawTest a0 a1 a2 a3 a4 a5 a6 a7 →
    reflectionTest0 a0 a1 a2 a3 a4 a5 a6 a7 ∨ reflectionTest1 a0 a1 a2 a3 a4 a5 a6 a7 ∨ reflectionTest2 a0 a1 a2 a3 a4 a5 a6 a7 := by
  unfold rotationTest lawTest reflectionTest0 reflectionTest1 reflectionTest2
  unfold rotation reflection0 reflection1 reflection2 op clip
  bv_check (config := { embeddedConstraintSubst := true }) "FiniteCertificate.lrat"

#print axioms certificate
end Definability.Cyclic1483.FiniteCertificate
