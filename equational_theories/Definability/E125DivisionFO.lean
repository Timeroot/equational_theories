import equational_theories.Definability.DivisionFO
import equational_theories.Definability.E63Family

/-!
# An unrestricted FO interpretation from E125 to E3954

The right division `d(x,y)=y*(y*x)` inverts the column through `y`.
Both graphs are given by the atomic formula `z*y=x`, read respectively
in the original operation and in `d`. The E125 rotation shows that `d`
satisfies E3954, so this does not need finite translation periods.
Duality also gives the E3548 target.
-/

namespace E63Family
variable {G : Type} [Magma G]

/-- E125's right division is the square of a left translation. -/
def rdiv125 (h : Equation125 G) : DivisionFO.RDiv (inferInstance : Magma G) where
  d x y := y ◇ (y ◇ x)
  inv x y := rotate_125 h x y
  can x y := (equation73_of_125 h x y).symm

/-- In right-division coordinates, the E125 rotation is precisely E3954. -/
theorem rdiv125_equation3954 (h : Equation125 G) :
    @Equation3954 G (rdiv125 h).magma := by
  let K := rdiv125 h
  intro x y
  change K.d x y = K.d (K.d y (K.d x y)) x
  let z := K.d x y
  have hx : z ◇ y = x := K.inv x y
  have hz : (z ◇ x) ◇ z = y := by
    calc
      (z ◇ x) ◇ z = (z ◇ (z ◇ y)) ◇ z := congrArg (fun w => (z ◇ w) ◇ z) hx.symm
      _ = y := rotate_125 h y z
  have hh := congrArg (fun w => K.d w z) hz
  dsimp only at hh
  rw [K.can] at hh
  calc
    z = K.d (z ◇ x) x := (K.can z x).symm
    _ = K.d (K.d y z) x := congrArg (fun w => K.d w x) hh

end E63Family

open Law Law.MagmaLaw
/-- E125 and its right-division companion are FO interdefinable on any carrier. -/
theorem Equation3954_structuralFrom_Equation125_rightDivision :
    Law3954.StructuralFrom Law125 := by
  intro G M hM
  have h : Equation125 G := Law125.models_iff.mp hM
  exact DivisionFO.structuralOn_rdiv M (E63Family.rdiv125 h)
    ((@Law3954.models_iff G (E63Family.rdiv125 h).magma).mpr
      (E63Family.rdiv125_equation3954 h))

spectrum_assert Equation3954_structuralFrom_Equation125_rightDivision complete

spectrum_assert E63Family.rdiv125_equation3954 complete
