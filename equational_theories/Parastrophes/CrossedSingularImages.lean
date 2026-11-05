import equational_theories.Parastrophes.PartitionedReductionImage
import equational_theories.Parastrophes.Equation477Image
import equational_theories.Parastrophes.Equation680Image
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# E477 and E680: no equational characterization of their division images

Both image criteria use the crossed cubic map c(x) = x*(x*x). They consist
of two identities together with bijectivity of c. In the three-part affine
families below, c(i,u) = (i,2u). Thus c is invertible over every field of odd
characteristic, but collapses each two-element fibre in characteristic two.

For E477 the additional identity is x*(x*c(x)) = x; for E680 it is
x*c(x) = c(x)*x. Each family satisfies its two identities over every
commutative ring. Their verification involves just nine pairs of parts and
ordinary ring identities, not enumeration of larger multiplication tables.

Every equation shared by the finite images holds in all odd-prime reductions,
hence over the integers, hence in the bad six-element reduction. That
reduction is not a left quasigroup. Consequently no set of magma equations
(in particular no single equation of any size) characterizes either image,
even among finite magmas. The four catalogue theorems register the finite
and arbitrary-carrier consequences; `bad_inherits` records the stronger fact.
-/

namespace Parastrophes.CrossedSingularImages
open Law

/-- The common three-element base is `i*j = 1-i-j` modulo three. -/
def colour : Fin 3 → Fin 3 → Fin 3 := ![![1,0,2], ![0,2,1], ![2,1,0]]

/-- Nine integer coefficient checks imply the crossed law over every ring. -/
def CrossCertificate (a b : Fin 3 → Fin 3 → Int) : Prop := ∀ i j,
  colour i (colour j i) = j ∧
  a i (colour j i) + b i (colour j i) * b j i = 0 ∧
  b i (colour j i) * a j i = 2

theorem crossed (a b : Fin 3 → Fin 3 → Int) (h : CrossCertificate a b)
    (R : Type) [CommRing R] (x y : Fin 3 × R) :
    (PartitionedReductionImage.family colour a b R).op x
      ((PartitionedReductionImage.family colour a b R).op y x) = (y.1, 2*y.2) := by
  obtain ⟨hc, ha, hb⟩ := h x.1 y.1
  have hA : (a x.1 (colour y.1 x.1) : R) +
      (b x.1 (colour y.1 x.1) : R) * (b y.1 x.1 : R) = 0 := by
    simpa only [map_add, map_mul, map_zero] using congrArg (Int.castRingHom R) ha
  have hB : (b x.1 (colour y.1 x.1) : R) * (a y.1 x.1 : R) = 2 := by
    simpa only [map_mul, map_ofNat] using congrArg (Int.castRingHom R) hb
  apply Prod.ext
  · exact hc
  · change (a x.1 (colour y.1 x.1) : R)*x.2 + (b x.1 (colour y.1 x.1) : R)*
      ((a y.1 x.1 : R)*y.2 + (b y.1 x.1 : R)*x.2) = 2*y.2
    linear_combination x.2*hA + y.2*hB

theorem double_injective (R : Type) [Field R] (h2 : (2 : R) ≠ 0) :
    Function.Injective (fun x : Fin 3 × R => (x.1, 2*x.2)) := by
  intro x y he
  have hc := congrArg Prod.fst he
  have hf := congrArg Prod.snd he
  have hh : x.2 = y.2 := mul_left_cancel₀ h2 hf
  exact Prod.ext hc hh

namespace E477

def left : Fin 3 → Fin 3 → Int := ![![2,1,2], ![-2,2,1], ![1,-2,-2]]
def right : Fin 3 → Fin 3 → Int := ![![-1,1,2], ![2,-1,1], ![-1,2,1]]

abbrev family (R : Type) [CommRing R] :=
  PartitionedReductionImage.family colour left right R

theorem coefficient_certificate : CrossCertificate left right := by
  unfold CrossCertificate
  decide

theorem core_eq (R : Type) [CommRing R] (x : Fin 3 × R) :
    Eq477Image.core (family R) x = (x.1, 2*x.2) :=
  crossed left right coefficient_certificate R x x

theorem diagonal_certificate : ∀ i : Fin 3,
    left i (colour i i) + right i (colour i i) * (left i i + 2*right i i) = 1 := by decide

theorem basis (R : Type) [CommRing R] : Eq477Image.Basis (family R) := by
  constructor
  · intro x
    change x = (family R).op x ((family R).op x (Eq477Image.core (family R) x))
    rw [core_eq]
    obtain ⟨hc, _, _⟩ := coefficient_certificate x.1 x.1
    have hh := diagonal_certificate x.1
    have hd : (left x.1 (colour x.1 x.1) : R) + (right x.1 (colour x.1 x.1) : R)*
        ((left x.1 x.1 : R) + 2*(right x.1 x.1 : R)) = 1 := by
      simpa only [map_add, map_mul, map_ofNat, map_one] using congrArg (Int.castRingHom R) hh
    apply Prod.ext
    · exact hc.symm
    · change x.2 = (left x.1 (colour x.1 x.1) : R)*x.2 +
        (right x.1 (colour x.1 x.1) : R)*((left x.1 x.1 : R)*x.2 +
          (right x.1 x.1 : R)*(2*x.2))
      linear_combination -x.2*hd
  · intro x y z
    exact (crossed left right coefficient_certificate R x y).trans
      (crossed left right coefficient_certificate R z y).symm

theorem prime_inImage (p : Nat) (hp : p.Prime) (hp2 : 2 < p) :
    InImage Law477 .left (family (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (Eq477Image.inImage_iff_core_injective _).mpr
  refine ⟨basis _, ?_⟩
  intro x y he
  rw [core_eq, core_eq] at he
  exact double_injective (ZMod p) (ReductionImage.two_ne_zero hp2) he

theorem bad_collision :
    (family (ZMod 2)).op (0,0) (2,0) = (family (ZMod 2)).op (0,0) (2,1) := by decide

theorem bad_not_leftQuasigroup : ¬ IsSideQuasigroup .left (family (ZMod 2)) := by
  intro h
  have he : (0 : ZMod 2) = 1 := congrArg Prod.snd ((h (0,0)).1 bad_collision)
  exact zero_ne_one he

theorem bad_inherits {K : NatMagmaLaw}
    (h : ∀ (A : Type) [Finite A] (D : Magma A), InImage Law477 .left D →
      @satisfies _ A D K) : @satisfies _ _ (family (ZMod 2)) K :=
  PartitionedReductionImage.bad_inherits colour left right prime_inImage h

end E477

namespace E680

def left : Fin 3 → Fin 3 → Int := ![![1,-2,1], ![2,1,-2], ![-2,2,2]]
def right : Fin 3 → Fin 3 → Int := ![![1,2,-1], ![-1,1,2], ![1,-1,2]]

abbrev family (R : Type) [CommRing R] :=
  PartitionedReductionImage.family colour left right R

theorem coefficient_certificate : CrossCertificate left right := by
  unfold CrossCertificate
  decide

theorem core_eq (R : Type) [CommRing R] (x : Fin 3 × R) :
    Eq477Image.core (family R) x = (x.1, 2*x.2) :=
  crossed left right coefficient_certificate R x x

theorem diagonal_certificate : ∀ i : Fin 3, left i i = right i i := by decide

theorem basis (R : Type) [CommRing R] : Eq680Image.Basis (family R) := by
  constructor
  · intro x y
    rw [core_eq]
    exact crossed left right coefficient_certificate R x y
  · intro x
    rw [core_eq]
    apply Prod.ext
    · rfl
    · change (left x.1 x.1 : R)*x.2 + (right x.1 x.1 : R)*(2*x.2) =
        (left x.1 x.1 : R)*(2*x.2) + (right x.1 x.1 : R)*x.2
      rw [diagonal_certificate]
      ring

theorem prime_inImage (p : Nat) (hp : p.Prime) (hp2 : 2 < p) :
    InImage Law680 .left (family (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (Eq680Image.inImage_iff_core_injective _).mpr
  refine ⟨basis _, ?_⟩
  intro x y he
  rw [core_eq, core_eq] at he
  exact double_injective (ZMod p) (ReductionImage.two_ne_zero hp2) he

theorem bad_collision :
    (family (ZMod 2)).op (0,0) (1,0) = (family (ZMod 2)).op (0,0) (1,1) := by decide

theorem bad_not_leftQuasigroup : ¬ IsSideQuasigroup .left (family (ZMod 2)) := by
  intro h
  have he : (0 : ZMod 2) = 1 := congrArg Prod.snd ((h (0,0)).1 bad_collision)
  exact zero_ne_one he

theorem bad_inherits {K : NatMagmaLaw}
    (h : ∀ (A : Type) [Finite A] (D : Magma A), InImage Law680 .left D →
      @satisfies _ A D K) : @satisfies _ _ (family (ZMod 2)) K :=
  PartitionedReductionImage.bad_inherits colour left right prime_inImage h

end E680
end Parastrophes.CrossedSingularImages

namespace Parastrophes.Catalogue
open Law CrossedSingularImages

/-- A six-element singular reduction defeats every finite image equation. -/
@[parastrophe_result] theorem left_noSingleEquation477_fin :
    ¬ SingleEquation .fin Law477 .left :=
  PartitionedReductionImage.obstruction colour E477.left E477.right
    E477.prime_inImage E477.bad_not_leftQuasigroup

/-- A six-element singular reduction defeats every finite image equation. -/
@[parastrophe_result] theorem left_noSingleEquation680_fin :
    ¬ SingleEquation .fin Law680 .left :=
  PartitionedReductionImage.obstruction colour E680.left E680.right
    E680.prime_inImage E680.bad_not_leftQuasigroup

/-- The finite obstruction also prevents an arbitrary-carrier characterization. -/
@[parastrophe_result] theorem left_noSingleEquation477_singular_all :
    ¬ SingleEquation .all Law477 .left :=
  fun h => left_noSingleEquation477_fin (singleEquation_finite h)

/-- The finite obstruction also prevents an arbitrary-carrier characterization. -/
@[parastrophe_result] theorem left_noSingleEquation680_all :
    ¬ SingleEquation .all Law680 .left :=
  fun h => left_noSingleEquation680_fin (singleEquation_finite h)

end Parastrophes.Catalogue
