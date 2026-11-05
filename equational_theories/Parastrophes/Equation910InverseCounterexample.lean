import equational_theories.Parastrophes.Equation883Extensions
import equational_theories.Parastrophes.Equation910Image

/-!
# A small extension testing E910 inverse terms

The thirteen-operation candidate below passed the ten previously saved E910
models, and the tested homogeneous scalar affine models. It fails on this
eight-element extension of `i*j=i+j+2` on Z/4. The F2 offset is nonzero
precisely when the first base index is 1 and the second is odd.

We reuse the general extension and division construction, and check just the
64 instances of the source law. This refutes this particular recovery term;
it does not exclude a different term or a single-equation image description.
-/
namespace Parastrophes.Eq910InverseCounterexample
open Eq883Extensions (extension divided seed seedDivision seed_division extension_division)

def offset : Fin 4 → Fin 4 → ZMod 2 :=
  ![![0,0,0,0], ![0,1,0,1], ![0,0,0,0], ![0,0,0,0]]

@[implicit_reducible] def source : Magma (Fin 4 × ZMod 2) :=
  extension seed 1 1 offset

@[implicit_reducible] def division : Magma (Fin 4 × ZMod 2) :=
  divided seedDivision 1 1 offset

theorem source_law : @Equation910 (Fin 4 × ZMod 2) source := by decide +kernel

theorem division_correct : IsDivision .left source division :=
  extension_division seed seedDivision seed_division 1 1 1 (by decide) offset

/-- The division therefore satisfies the established partial image criterion. -/
theorem division_equation427 : @Equation427 (Fin 4 × ZMod 2) division :=
  Eq910Image.forward source division division_correct source_law

def inverse13 {G : Type} (D : Magma G) (x y : G) : G :=
  D.op (D.op (D.op x y) (D.op (D.op x (D.op y y)) x))
    (D.op (D.op y y) (D.op y (D.op (D.op x (D.op x x)) (D.op x y))))

theorem inverse13_fails :
    inverse13 division (0,0) (1,0) ≠ source.op (0,0) (1,0) := by decide +kernel

end Parastrophes.Eq910InverseCounterexample
