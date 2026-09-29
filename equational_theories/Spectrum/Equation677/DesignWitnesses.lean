import equational_theories.Spectrum.Equation677.DesignModels
import equational_theories.Spectrum.QuarticSeeds

/-! Compact, symbolic E677 witnesses at orders 6487, 6493, and 6499.

The construction data are the prime powers 2^4 and 3^4, the scalar coefficient
pairs (2,4), (4,1), (9,11), (7,3), and the truncation sizes 7,13,19.
The proofs use a general gluing theorem and polynomial identities, never an
enumeration of the large models' pairs. No `sorry` or native checking is used.
-/
namespace Spectrum.E677
open Law Law.MagmaLaw

def scalar {R : Type*} [CommRing R] (a b : R) (x y : R) := a*x+b*y

theorem scalar_lawful {R : Type*} [CommRing R] (a b : R)
    (hx : a*b+a*b^3=1) (hy : a+a^2*b^2+b^3=0) : Lawful (scalar a b) := by
  intro x y
  dsimp [scalar]
  linear_combination x*hx + y*hy

theorem scalar_model {n : ℕ} [NeZero n] (a b : ZMod n)
    (hx : a*b+a*b^3=1) (hy : a+a^2*b^2+b^3=0) : Model (Fin n) := by
  have h : Model (ZMod n) := ⟨scalar a b, scalar_lawful a b hx hy, by simp⟩
  exact h.relabel (ZMod.finEquiv n).toEquiv.symm

theorem scalar_idempotent {n : ℕ} [NeZero n] (a b : ZMod n)
    (hx : a*b+a*b^3=1) (hy : a+a^2*b^2+b^3=0) (hi : a+b=1) :
    Model (Fin n) true := by
  have h : Model (ZMod n) true := ⟨scalar a b, scalar_lawful a b hx hy, by
    intro _ x
    dsimp [scalar]
    linear_combination x*hi⟩
  exact h.relabel (ZMod.finEquiv n).toEquiv.symm

theorem quartic (n : ℕ) [NeZero n] : Model (Fin (n^4)) true := by
  let A := ZMod n × ZMod n × ZMod n × ZMod n
  have h : Model A true := ⟨QuarticSeeds.op 1 (-1) 1 (-1),
    fun x y => (QuarticSeeds.law_677 x y).symm,
    fun _ => QuarticSeeds.idempotent _ _ _ _⟩
  exact h.relabel (Fintype.equivFinOfCardEq (by simp [A, pow_succ, Nat.mul_assoc]))

theorem idem5 : Model (Fin 5) true :=
  scalar_idempotent 2 4 (by decide) (by decide) (by decide)

theorem idem80 : Model (Fin 80) true :=
  (idem5.product (quartic 2)).relabel (Fintype.equivFinOfCardEq (by simp))

theorem idem81 : Model (Fin 81) true := quartic 3

theorem seed7 : Model (Fin 7) := scalar_model 4 1 (by decide) (by decide)
theorem seed13 : Model (Fin 13) := scalar_model 9 11 (by decide) (by decide)
theorem seed19 : Model (Fin 19) := scalar_model 7 3 (by decide) (by decide)

theorem model19 : Law677.HasModel 19 := seed19.hasModel
theorem model80 : Law677.HasModel 80 := idem80.hasModel

/-- The uniform construction: any TD(81,q) and q-model can fill these holes. -/
theorem eighty_groups {q r : ℕ} (D : PBD.HasTD 81 q) (hr : r ≤ q)
    (g : Model (Fin q)) (h : Model (Fin r)) : Law677.HasModel (80*q+r) :=
  hasTD_models D hr g h idem80 idem81

theorem td81 : PBD.HasTD 81 81 :=
  PBD.HasTD.primePower (p := 3) (e := 4) (by decide) (by decide) (by decide)

theorem model6487 : Law677.HasModel 6487 :=
  eighty_groups td81 (by decide) idem81.forget seed7

theorem model6493 : Law677.HasModel 6493 :=
  eighty_groups td81 (by decide) idem81.forget seed13

theorem model6499 : Law677.HasModel 6499 :=
  eighty_groups td81 (by decide) idem81.forget seed19

spectrum_assert model6487 complete
spectrum_assert model6493 complete
spectrum_assert model6499 complete
spectrum_assert model19 complete
spectrum_assert model80 complete

/-- info: 'Spectrum.E677.model6487' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model6487
/-- info: 'Spectrum.E677.model6493' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model6493
/-- info: 'Spectrum.E677.model6499' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model6499

end Spectrum.E677
