import equational_theories.Parastrophes.TranslationLoops
import equational_theories.Superposition

/-!
# E1370's exact left-division image

Write `S(x)=x*x` and `u=S(z*y)*y`. The single identity is
`x=y*(S(S(u))*x)`, with twenty-one operations when expanded.
It is equivalent to E127 together with `x=y*(u*x)`. The extra squaring
forces the cancellation identity that the shorter candidate alone lacks.
-/
namespace Parastrophes
open Law FreeMagma

namespace Eq1370Image

def square {G : Type*} (M : Magma G) (x : G) : G := M.op x x

/-- The extra squaring enforces E127. Naming the square map keeps this
pure equational derivation small. -/
private theorem forces127 {G : Type} (M : Magma G) (S : G → G)
    (hS : ∀ x, M.op x x = S x)
    (h : ∀ x y z, M.op y (M.op (S (S (M.op (S (M.op z y)) y))) x) = x) :
    ∀ x y, M.op y (M.op (S y) x) = x := by
  have e7 (X0 : G) : (M.op X0 X0) = (S X0) :=
    hS ..
  have e8 (X0 X1 X2 : G) : (M.op X1 (M.op (S (S (M.op (S (M.op X2 X1)) X1))) X0)) = X0 :=
    h ..
  have e10 (X0 X1 : G) : (M.op X0 (M.op (S (S (M.op (S (S X0)) X0))) X1)) = X1 :=
    superpose e7 e8
  have e13 (X0 X1 X2 X3 : G) : (M.op X1 X0) = (M.op (S (S (M.op (S (M.op X3 (S (S (M.op (S (M.op X2 X1)) X1))))) (S (S (M.op (S (M.op X2 X1)) X1)))))) X0) :=
    superpose e8 e8
  have e58 (X0 X1 X2 : G) : (M.op (S (S (M.op (S (M.op X2 X0)) X0))) (M.op X0 X1)) = X1 :=
    superpose e13 e8
  have e80 (X0 X1 : G) : (M.op (S (S (M.op (S (M.op X1 X0)) X0))) (S X0)) = X0 :=
    superpose e7 e58
  have e82 (X0 X1 X2 : G) : (M.op (S (S (M.op (S (M.op X1 X2)) X2))) X0) = (M.op (S (S (M.op (S (S X2)) X2))) X0) :=
    superpose e10 e58
  have e95 (X0 : G) : (M.op (S (S (M.op (S (S X0)) X0))) (S X0)) = X0 :=
    superpose e82 e80
  have e141 (X0 X1 : G) : (M.op (S (S (M.op (S X0) (S X0)))) (M.op (S X0) X1)) = X1 :=
    superpose e95 e58
  have e148 (X0 X1 : G) : (M.op (S (S (S (S X0)))) (M.op (S X0) X1)) = X1 :=
    superpose e7 e141
  have e249 (X0 : G) : (S X0) = (M.op (S (S (S (S X0)))) (S (S X0))) :=
    superpose e7 e148
  have e333 (X0 : G) : (S (S X0)) = (M.op (S (S (S X0))) (S (S (S X0)))) :=
    superpose e249 e95
  have e358 (X0 : G) : (S (S X0)) = (S (S (S (S X0)))) :=
    superpose e7 e333
  have e412 (X0 X1 : G) : (M.op (S (S X0)) (M.op (S X0) X1)) = X1 :=
    superpose e358 e148
  have e427 (X0 : G) : (S (S (S X0))) = (M.op (S (S (S (S X0)))) (S (S X0))) :=
    superpose e358 e249
  have e446 (X0 : G) : (S X0) = (S (S (S X0))) :=
    superpose e249 e427
  have e794 (X0 X1 : G) : (M.op X1 X0) = (M.op (S (M.op (S (S X1)) X1)) X0) :=
    superpose e412 e10
  have e1636 (X0 X1 : G) : (M.op X0 (M.op (S (S (M.op X0 X0))) X1)) = X1 :=
    superpose e794 e8
  have e1693 (X0 X1 : G) : (M.op X0 (M.op (S (S (S X0))) X1)) = X1 :=
    superpose e7 e1636
  have e1717 (X0 X1 : G) : (M.op X0 (M.op (S X0) X1)) = X1 :=
    superpose e446 e1693
  exact fun x y => e1717 y x

/-- The shorter two-axiom description of the image. -/
def Basis {G : Type} (M : Magma G) : Prop :=
  @Equation127 G M ∧ ∀ x y z,
    x = M.op y (M.op (M.op (square M (M.op z y)) y) x)

theorem leftQuasigroup127 {G : Type} (M : Magma G) (h : @Equation127 G M) :
    IsSideQuasigroup .left M :=
  leftQuasigroup_of_translationLoops M (fun y => [M.op y y])
    (fun y x => (h x y).symm)

/-- Squaring is an involution in E127. -/
theorem square_square {G : Type} (M : Magma G) (h : @Equation127 G M) (x : G) :
    square M (square M x) = x :=
  ((leftQuasigroup127 M h x).1 (h (M.op x x) x)).symm

end Eq1370Image

/-- E307556419314087120878580960 in the extended numbering. -/
def leftImage1370 : NatMagmaLaw :=
  let u := ((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ Lf 1
  let v := u ⋆ u
  ⟨Lf 0, Lf 1 ⋆ ((v ⋆ v) ⋆ Lf 0)⟩

theorem leftImage1370_iff {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage1370 ↔ ∀ x y z,
      x = M.op y (M.op (Eq1370Image.square M (Eq1370Image.square M
        (M.op (Eq1370Image.square M (M.op z y)) y))) x) := by
  constructor
  · intro h x y z
    exact h (fun n => if n = 0 then x else if n = 1 then y else z)
  · intro h v
    exact h (v 0) (v 1) (v 2)

namespace Eq1370Image

theorem iff_basis {G : Type} (M : Magma G) :
    @satisfies _ G M leftImage1370 ↔ Basis M := by
  constructor
  · intro hM
    have h := (leftImage1370_iff M).mp hM
    have h127 : @Equation127 G M := fun x y =>
      (forces127 M (square M) (fun _ => rfl) (fun x y z => (h x y z).symm) x y).symm
    refine ⟨h127, ?_⟩
    intro x y z
    simpa only [square_square M h127] using h x y z
  · rintro ⟨h127, h6⟩
    apply (leftImage1370_iff M).mpr
    intro x y z
    rw [square_square M h127]
    exact h6 x y z

/-- Reverse multiplication is simply `(x*x)*y` in the division operation. -/
theorem forward {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation1370 G M) : Basis D := by
  have eD1 (x y : G) : M.op x (D.op x y) = y := hd.1 x y
  have eD2 (x y : G) : D.op x (M.op x y) = y := hd.2 x y
  have e8 (x y z : G) : M.op y (M.op (M.op (M.op z y) y) x) = x := (h x y z).symm
  have e14 (x y z : G) : M.op y x = D.op (M.op (M.op z y) y) x := superpose eD1 e8
  have e16 (x y z : G) : M.op (M.op (M.op z y) y) x = D.op y x := superpose e8 eD2
  have e32 (x y : G) : M.op x y = D.op (D.op x x) y := superpose e16 e14
  have e36 (x y z : G) : M.op y z = D.op (M.op (D.op x y) y) z := superpose e16 e14
  constructor
  · intro x y
    rw [← e32, hd.2]
  · intro x y z
    change x = D.op y (D.op (D.op (D.op (D.op z y) (D.op z y)) y) x)
    rw [← e32, ← e36, hd.2]

/-- Both parts of the shorter description rotate back to E1370. -/
theorem backward {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : Basis M) : @Equation1370 G D := by
  have eD1 (x y : G) : M.op x (D.op x y) = y := hd.1 x y
  have eD2 (x y : G) : D.op x (M.op x y) = y := hd.2 x y
  have e9 (x y z : G) : M.op y (M.op (M.op (M.op (M.op z y) (M.op z y)) y) x) = x :=
    (h.2 x y z).symm
  have e10 (x y : G) : M.op y (M.op (M.op y y) x) = x := (h.1 x y).symm
  have e16 (x y : G) : M.op (M.op y y) x = D.op y x := superpose e10 eD2
  have e25 (x y z : G) : M.op y x = D.op (M.op (M.op (M.op z y) (M.op z y)) y) x :=
    superpose eD1 e9
  have e28 (x y z : G) : M.op (M.op (M.op (M.op z y) (M.op z y)) y) x = D.op y x :=
    superpose e9 eD2
  have e31 (x y z : G) : D.op y x = M.op (D.op (M.op z y) y) x := superpose e16 e28
  have e34 (x y z : G) : M.op y x = D.op (D.op (M.op z y) y) x := superpose e16 e25
  have e117 (x y z : G) : M.op y z = D.op (D.op (D.op x y) y) z := superpose e31 e34
  intro x y z
  rw [← e117, hd.2]

end Eq1370Image

namespace Catalogue

/-- The forward division operation is the three-operation term
`((x*x)*x)*y`; no search or choice is needed to compute it. -/
@[parastrophe_result] theorem left_term1370_all :
    UniformTermWitness .all Law1370 .left (((Lf 0 ⋆ Lf 0) ⋆ Lf 0) ⋆ Lf 1) := by
  intro G M _ hM
  have h := (@Law1370.models_iff G M).mp hM
  have hQ := leftQuasigroup_of_translationLoops M
    (fun y => [M.op (M.op y y) y]) (fun y x => (h x y y).symm)
  constructor
  · intro x y
    exact (h y x x).symm
  · intro x y
    exact (hQ x).1 (h (M.op x y) x x).symm

/-- The inverse operation in the long target is simply `(x*x)*y`. -/
theorem leftImage1370_term_all :
    UniformTermWitness .all leftImage1370 .left ((Lf 0 ⋆ Lf 0) ⋆ Lf 1) := by
  intro G M _ hM
  have h := ((Eq1370Image.iff_basis M).mp hM).1
  have hQ := Eq1370Image.leftQuasigroup127 M h
  constructor
  · intro x y
    exact (h y x).symm
  · intro x y
    exact (hQ x).1 (h (M.op x y) x).symm

/-- E1370's left-division image has this single identity on arbitrary carriers. -/
@[parastrophe_result] theorem left_characterizes1370_all_long :
    Characterizes .all Law1370 .left leftImage1370 := by
  apply characterizes_of_division
  · intro G M _ h
    exact Eq1370Image.leftQuasigroup127 M ((Eq1370Image.iff_basis M).mp h).1
  · intro G M D _ hd h
    exact (Eq1370Image.iff_basis D).mpr
      (Eq1370Image.forward M D hd ((@Law1370.models_iff G M).mp h))
  · intro G M D _ hd h
    exact (@Law1370.models_iff G D).mpr
      (Eq1370Image.backward M D hd ((Eq1370Image.iff_basis M).mp h))

/-- The correspondence preserves labelled and unlabelled model counts,
including on infinite carriers. -/
theorem sameFineSpectrum1370_leftImage : SameFineSpectrum .all Law1370 leftImage1370 :=
  characterizes_sameFineSpectrum left_characterizes1370_all_long
    (fun G M _ h => sideQuasigroup_of_division (left_term1370_all G M trivial h))

end Catalogue
end Parastrophes
