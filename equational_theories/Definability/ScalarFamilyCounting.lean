import equational_theories.Definability.AffineFamilyCounting
import Mathlib.Data.Fintype.BigOperators

/-! Exact scalar-affine tests and counts that reuse multiplication-kernel sizes. -/
open Law FreeMagma
open scoped BigOperators
namespace Magma.ScalarFamily
variable {R : Type} [CommRing R] {k : ℕ}

def linear (a b : R) : FreeMagma (Fin k) → Fin k → R
  | .Leaf j => fun i => if i = j then 1 else 0
  | .Fork l r => fun i => a * linear a b l i + b * linear a b r i

def constant (a b : R) : FreeMagma (Fin k) → R
  | .Leaf _ => 0
  | .Fork l r => a * constant a b l + b * constant a b r + 1

theorem eval_formula (a b c : R) (φ : Fin k → R) (t : FreeMagma (Fin k)) :
    @evalInMagma _ _ ⟨AffineFamily.op (a,b,c)⟩ φ t =
      (∑ i, linear a b t i * φ i) + constant a b t * c := by
  letI : Magma R := ⟨AffineFamily.op (a,b,c)⟩
  induction t with
  | Leaf j => simp [evalInMagma, linear, constant]
  | Fork l r hl hr =>
    change AffineFamily.op (a,b,c) (evalInMagma φ l) (evalInMagma φ r) = _
    rw [hl, hr]
    simp only [AffineFamily.op, linear, constant, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
    ring

def LinearTest (L : MagmaLaw (Fin k)) (a b : R) : Prop := linear a b L.lhs = linear a b L.rhs
def delta (L : MagmaLaw (Fin k)) (a b : R) : R := constant a b L.lhs - constant a b L.rhs
def Test (L : MagmaLaw (Fin k)) (p : AffineFamily.P R) : Prop :=
  LinearTest L p.1 p.2.1 ∧ delta L p.1 p.2.1 * p.2.2 = 0
instance [DecidableEq R] (L : MagmaLaw (Fin k)) (a b : R) : Decidable (LinearTest L a b) := by
  unfold LinearTest; infer_instance
instance [DecidableEq R] (L : MagmaLaw (Fin k)) (p : AffineFamily.P R) : Decidable (Test L p) := by
  unfold Test; infer_instance

theorem test_iff_satisfies (L : MagmaLaw (Fin k)) (p : AffineFamily.P R) :
    Test L p ↔ @satisfies _ R ⟨AffineFamily.op p⟩ L := by
  rcases p with ⟨a,b,c⟩
  letI : Magma R := ⟨AffineFamily.op (a,b,c)⟩
  constructor
  · rintro ⟨hl,hc⟩ φ
    change evalInMagma φ L.lhs = evalInMagma φ L.rhs
    simp only [eval_formula]
    have hc' : constant a b L.lhs * c = constant a b L.rhs * c := by
      simpa only [delta, sub_mul, sub_eq_zero] using hc
    rw [show linear a b L.lhs = linear a b L.rhs from hl, hc']
  · intro h
    have hc := h (fun _ => 0)
    change evalInMagma (fun _ => 0) L.lhs = evalInMagma (fun _ => 0) L.rhs at hc
    simp only [eval_formula, mul_zero, Finset.sum_const_zero, zero_add] at hc
    constructor
    · funext j
      have hj := h (Pi.single j 1)
      change evalInMagma (Pi.single j 1) L.lhs = evalInMagma (Pi.single j 1) L.rhs at hj
      simpa [eval_formula, Pi.single_apply, hc] using hj
    · simpa only [delta, sub_mul, sub_eq_zero] using hc

variable [Fintype R] [DecidableEq R]
def kernelCount (r : R) : ℕ := Fintype.card {c : R // r*c=0}
def count (L : MagmaLaw (Fin k)) : ℕ :=
  ∑ a : R, ∑ b : R, if LinearTest L a b then kernelCount (delta L a b) else 0

theorem card_test (L : MagmaLaw (Fin k)) :
    Fintype.card {p : AffineFamily.P R // Test L p} = count (R := R) L := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (a : R) (bc : R × R) => Test L (a,bc)))]
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun b c : R => Test L (a,b,c)))]
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : LinearTest L a b
  · simp only [if_pos h, kernelCount]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun c => by simp [Test, h])
  · simp [Test, h]

/-- Materialize each kernel size once before scanning coefficient pairs. -/
def memoFinite (f : R → ℕ) : R → ℕ :=
  let table := (Finset.univ : Finset R).map
    ⟨fun r => (r, f r), fun _ _ h => congrArg Prod.fst h⟩
  fun x => ∑ p ∈ table, if p.1 = x then p.2 else 0
omit [CommRing R] in
@[simp] theorem memoFinite_eq (f : R → ℕ) : memoFinite f = f := by
  funext x
  simp [memoFinite]

def countCached (L : MagmaLaw (Fin k)) : ℕ :=
  let table := (Finset.univ : Finset R).map
    ⟨fun r => (r, kernelCount r), fun _ _ h => congrArg Prod.fst h⟩
  ∑ a : R, ∑ b : R, if LinearTest L a b then
    (let value := delta L a b
     ∑ p ∈ table, if p.1 = value then p.2 else 0) else 0
@[csimp] theorem count_eq_cached : @count = @countCached := by
  funext R inst k ft de L
  simp [count, countCached]
end Magma.ScalarFamily

/-- info: 'Magma.ScalarFamily.test_iff_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.ScalarFamily.test_iff_satisfies
/-- info: 'Magma.ScalarFamily.card_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.ScalarFamily.card_test
