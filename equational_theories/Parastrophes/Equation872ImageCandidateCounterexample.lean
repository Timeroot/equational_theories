import equational_theories.Parastrophes.Equation872ImageCandidate
import Mathlib.Data.ZMod.Basic

/-! Finite counterexamples to proposed one-equation image characterizations.
The six-element model refutes four longer image candidates.
The two displayed identities have indices 10613 and 11985 in the rewrite audit;
interchanging y and z gives indices 10881 and 12992. These are research indices,
not equation numbers. All four identities hold, but the exact image basis fails.
A 25-element affine model also refutes the 20-operation candidate 3652.
-/
namespace Parastrophes.Eq872ImageCandidate.Counterexample
open Law Eq872Image

def candidateA {G : Type} (D : Magma G) : Prop := ∀ x y z,
  x = D.op (middle D (D.op z x) y)
    (D.op (D.op x (D.op (core D z) (D.op x z))) (D.op z x))

def candidateB {G : Type} (D : Magma G) : Prop := ∀ x y z,
  x = D.op (D.op (middle D (D.op x z) y) (D.op x (D.op x z)))
    (D.op (core D x) (D.op z x))

/-- Two fibres over an abelian group: translation within a fibre and
subtraction between fibres. -/
@[implicit_reducible] def folded {R : Type} [AddCommGroup R] (e : R) :
    Magma (Bool × R) := ⟨fun x y =>
      (y.1, if x.1 = y.1 then y.2 + e else x.2 - y.2)⟩

@[simp] theorem folded_op {R : Type} [AddCommGroup R] (e : R) (x y : Bool × R) :
    (folded e).op x y = (y.1, if x.1 = y.1 then y.2 + e else x.2 - y.2) := rfl

theorem folded_satisfies_A {R : Type} [AddCommGroup R] (e : R)
    (he : (3 : ℤ) • e = 0) : candidateA (folded e) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ ⟨c,z⟩
  cases a <;> cases b <;> cases c <;>
    simp [middle, core] <;> abel_nf <;> simpa using he

theorem folded_satisfies_B {R : Type} [AddCommGroup R] (e : R)
    (he : (3 : ℤ) • e = 0) : candidateB (folded e) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ ⟨c,z⟩
  cases a <;> cases b <;> cases c <;>
    simp [middle, core] <;> abel_nf <;> simpa using he

theorem folded_not_image {R : Type} [AddCommGroup R] (e : R) (he : e ≠ 0) :
    ¬ InImage Law872 .left (folded e) := by
  rintro ⟨M, hM, hd⟩
  have hb := Eq872Image.forward M (folded e) hd ((@Law872.models_iff _ M).mp hM)
  have h := hb.2 (false, 0) (true, 0)
  simp [core, he] at h

/-- The six-element instance stored in the research record. -/
@[implicit_reducible] def magma : Magma (Bool × ZMod 3) := folded 1

theorem satisfies_A : candidateA magma := folded_satisfies_A 1 (by decide)
theorem satisfies_B : candidateB magma := folded_satisfies_B 1 (by decide)
theorem not_image : ¬ InImage Law872 .left magma := folded_not_image 1 (by decide)

theorem refutes_A :
    ¬ (∀ (G : Type) [Finite G] (D : Magma G), candidateA D ↔ InImage Law872 .left D) := by
  intro h
  exact not_image ((h (Bool × ZMod 3) magma).mp satisfies_A)

theorem refutes_B :
    ¬ (∀ (G : Type) [Finite G] (D : Magma G), candidateB D ↔ InImage Law872 .left D) := by
  intro h
  exact not_image ((h (Bool × ZMod 3) magma).mp satisfies_B)

/-- info: 'Parastrophes.Eq872ImageCandidate.Counterexample.refutes_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refutes_A

/-- Multiplication by a square root of 3 on two coordinates over `Z/5Z`.
The resulting operation is affine over the field of 25 elements. -/
@[implicit_reducible] def field25 : Magma (ZMod 5 × ZMod 5) :=
  ⟨fun x y => (x.1 + 3*y.2, x.2 + y.1)⟩

@[simp] theorem field25_op (x y : ZMod 5 × ZMod 5) :
    field25.op x y = (x.1 + 3*y.2, x.2 + y.1) := rfl

/-- The shortest candidate also fails: a coordinate calculation suffices,
without checking the 25³ assignments separately. -/
theorem field25_satisfies : Candidate field25 := by
  rintro ⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩
  simp only [middle, index, core, field25_op, Prod.mk.injEq]
  have h5 : (5 : ZMod 5) = 0 := by decide
  constructor
  · linear_combination -(13*a + 9*b + 2*c + 18*d + 6*e + 6*f) * h5
  · linear_combination -(3*a + 13*b + 6*c + 2*d + 2*e + 6*f) * h5

theorem field25_not_image : ¬ InImage Law872 .left field25 := by
  rintro ⟨M, hM, hd⟩
  have hb := Eq872Image.forward M field25 hd ((@Law872.models_iff _ M).mp hM)
  have h := hb.2 (0, 0) (1, 0)
  norm_num [core] at h
  exact (by decide : (0 : ZMod 5) ≠ 4) h

/-- The counterexample already has bijective translations on both sides. -/
theorem field25_quasigroup : IsQuasigroup field25 := by
  constructor
  · exact left_quasigroup_fin field25 field25_satisfies
  · intro y
    have hi : Function.Injective (fun x => field25.op x y) := by
      intro x z h
      exact Prod.ext (add_right_cancel (congrArg Prod.fst h))
        (add_right_cancel (congrArg Prod.snd h))
    exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

theorem refutes_candidate :
    ¬ (∀ (G : Type) [Finite G] (D : Magma G), Candidate D ↔ InImage Law872 .left D) := by
  intro h
  exact field25_not_image ((h (ZMod 5 × ZMod 5) field25).mp field25_satisfies)

/-- info: 'Parastrophes.Eq872ImageCandidate.Counterexample.refutes_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms refutes_candidate

end Parastrophes.Eq872ImageCandidate.Counterexample
