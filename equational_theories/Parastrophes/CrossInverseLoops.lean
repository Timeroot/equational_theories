import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.LinearCombination
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Finite cross-inverse loops and E1496 models

A normalized central extension of a field gives cross-inverse loops whose
inverse permutations have unbounded order in finite characteristic. Taking a
Cartesian square supplies a square root of the inverse automorphism; twisting
one input by this square root gives an E1496 division image.

These constructions do not settle whether the finite image is characterized
by one equation. In particular, unbounded inverse periods alone do not rule
out a uniform inverse term.
-/
namespace Parastrophes.CrossInverseLoops

section Central
variable {K : Type} [Field K] [DecidableEq K]

/-- The three exceptional lines are stable under `(x,y) ↦ (x+y,-x)`. -/
def correction (x y : K) : K :=
  if x = 0 ∨ y = 0 then 0 else if x + y = 0 then x else (x-y)/3

@[simp] theorem correction_zero_left (y : K) : correction 0 y = 0 := by
  simp [correction]
@[simp] theorem correction_zero_right (x : K) : correction x 0 = 0 := by
  simp [correction]
@[simp] theorem correction_inverse (x : K) : correction x (-x) = x := by
  by_cases h : x = 0 <;> simp [correction, h]

theorem correction_cross (h3 : (3 : K) ≠ 0) (x y : K) :
    correction x y + correction (x+y) (-x) = x := by
  by_cases hx : x = 0
  · subst x; simp
  by_cases hy : y = 0
  · subst y; simp
  by_cases hxy : x+y = 0
  · simp [correction, hx, hy, hxy]
  have hneg : -x ≠ 0 := neg_ne_zero.mpr hx
  have hsum : x+y+-x ≠ 0 := by
    have he : x+y+-x = y := by ring
    rwa [he]
  simp only [correction, hx, hy, hxy, hneg, hsum, or_self, if_false]
  field_simp
  ring

theorem correction_neg (x y : K) : correction (-x) (-y) = -correction x y := by
  have hsum : (-x + -y = 0) ↔ (x+y=0) := by rw [← neg_add, neg_eq_zero]
  simp only [correction, neg_eq_zero, hsum]
  split_ifs <;> ring

abbrev Point (K : Type) := K × K

def op (a b : Point K) : Point K :=
  (a.1+b.1, a.2+b.2+correction a.1 b.1)

def inv (a : Point K) : Point K := (-a.1, -a.2-a.1)
def invBack (a : Point K) : Point K := (-a.1, -a.2+a.1)

@[simp] theorem op_zero (a : Point K) : op a (0,0) = a := by
  ext <;> simp [op]
@[simp] theorem zero_op (a : Point K) : op (0,0) a = a := by
  ext <;> simp [op]

omit [DecidableEq K] in
@[simp] theorem inv_invBack (a : Point K) : inv (invBack a) = a := by
  ext <;> simp [inv, invBack]
omit [DecidableEq K] in
@[simp] theorem invBack_inv (a : Point K) : invBack (inv a) = a := by
  ext <;> simp [inv, invBack]

def inverseEquiv : Point K ≃ Point K where
  toFun := inv
  invFun := invBack
  left_inv := invBack_inv
  right_inv := inv_invBack

/-- The right inverse is an automorphism, and its square is a nontrivial shear. -/
theorem inv_op (a b : Point K) : inv (op a b) = op (inv a) (inv b) := by
  ext <;> simp only [inv, op, correction_neg] <;> ring

omit [DecidableEq K] in
theorem inv_twice (a : Point K) : inv (inv a) = (a.1, a.2+2*a.1) := by
  ext <;> simp only [inv] <;> ring

theorem cross_right (h3 : (3 : K) ≠ 0) (a b : Point K) :
    op (op a b) (inv a) = b := by
  ext
  · simp [op, inv]
  · change a.2+b.2+correction a.1 b.1+(-a.2-a.1)+
      correction (a.1+b.1) (-a.1) = b.2
    linear_combination correction_cross h3 a.1 b.1

/-- Each row is injective, directly from the crossed-inverse identity. -/
theorem left_injective (h3 : (3 : K) ≠ 0) (a : Point K) :
    Function.Injective (op a) := by
  intro b c h
  have hh := congrArg (fun z => op z (inv a)) h
  simpa only [cross_right h3] using hh

theorem right_injective (b : Point K) : Function.Injective (fun a => op a b) := by
  rintro ⟨x,u⟩ ⟨y,v⟩ h
  have hxy : x = y := add_right_cancel (congrArg Prod.fst h)
  subst y
  have huv := congrArg Prod.snd h
  dsimp [op] at huv
  have huv' := add_right_cancel (add_right_cancel huv)
  exact congrArg (Prod.mk x) huv'

theorem cross_left (h3 : (3 : K) ≠ 0) (a b : Point K) :
    op a (op b (inv a)) = b := by
  apply right_injective (inv a)
  exact cross_right h3 a (op b (inv a))

/-- A square root of the inverse permutation on the Cartesian square. -/
abbrev Carrier (K : Type) := Point K × Point K

def turn (a : Carrier K) : Carrier K := (a.2, inv a.1)
def unturn (a : Carrier K) : Carrier K := (invBack a.2, a.1)

omit [DecidableEq K] in
@[simp] theorem turn_unturn (a : Carrier K) : turn (unturn a) = a := by
  simp [turn, unturn]
omit [DecidableEq K] in
@[simp] theorem unturn_turn (a : Carrier K) : unturn (turn a) = a := by
  simp [turn, unturn]

@[implicit_reducible] def division : Magma (Carrier K) :=
  ⟨fun a b => (op a.1 b.2, op a.2 (inv b.1))⟩

/-- The same twisted cyclic identity used in the infinite completion model. -/
theorem division_cross (h3 : (3 : K) ≠ 0) (a b : Carrier K) :
    division.op b (division.op a b) = turn a := by
  apply Prod.ext
  · exact cross_left h3 b.1 a.2
  · change op b.2 (inv (op a.1 b.2)) = inv a.1
    rw [inv_op, cross_left h3]

theorem division_cross_twice (h3 : (3 : K) ≠ 0) (a b : Carrier K) :
    division.op (division.op a b) (turn a) = turn b := by
  have h := division_cross h3 b (division.op a b)
  rwa [division_cross h3 a b] at h

theorem division_left_injective (h3 : (3 : K) ≠ 0) (a : Carrier K) :
    Function.Injective (division.op a) := by
  intro b c h
  apply Function.LeftInverse.injective unturn_turn
  rw [← division_cross_twice h3 a b, ← division_cross_twice h3 a c, h]

@[implicit_reducible] def source : Magma (Carrier K) :=
  ⟨fun a b => division.op (unturn b) a⟩

theorem isDivision (h3 : (3 : K) ≠ 0) :
    IsDivision .left (division (K := K)) source := by
  have hi (a b : Carrier K) : division.op a (source.op a b) = b := by
    change division.op a (division.op (unturn b) a) = b
    rw [division_cross h3, turn_unturn]
  exact ⟨hi, fun a b => division_left_injective h3 a (hi a (division.op a b))⟩

@[simp] theorem division_zero (a : Carrier K) : division.op a ((0,0),(0,0)) = a := by
  change (op a.1 (0,0), op a.2 (inv (0,0))) = a
  simp [inv]
@[simp] theorem zero_division (a : Carrier K) : division.op ((0,0),(0,0)) a = turn a := by
  change (op (0,0) a.2, op (0,0) (inv a.1)) = turn a
  simp [turn]

/-- All squares of the source operation are the distinguished right identity. -/
theorem source_square (h3 : (3 : K) ≠ 0) (a : Carrier K) :
    source.op a a = ((0,0),(0,0)) := by
  apply division_left_injective h3 a
  rw [(isDivision h3).1, division_zero]

@[simp] theorem source_zero (a : Carrier K) : source.op a ((0,0),(0,0)) = turn a := by
  change division.op (unturn ((0,0),(0,0))) a = turn a
  have hz : unturn (((0,0),(0,0)) : Carrier K) = ((0,0),(0,0)) := by
    simp [unturn, invBack]
  rw [hz, zero_division]

theorem source_law1496 (h3 : (3 : K) ≠ 0) : @Equation1496 (Carrier K) source := by
  intro x y z
  rw [source_square h3, source_zero]
  change x = division.op (unturn (turn y)) (source.op y x)
  rw [unturn_turn]
  exact ((isDivision h3).1 y x).symm

theorem source_law1492 (h3 : (3 : K) ≠ 0) : @Equation1492 (Carrier K) source :=
  fun x y => source_law1496 h3 x y y

omit [DecidableEq K] in
/-- Four turns shear both central coordinates by twice their base coordinate. -/
theorem turn_four (a : Carrier K) :
    turn^[4] a = ((a.1.1, a.1.2+2*a.1.1), (a.2.1, a.2.2+2*a.2.1)) := by
  change (inv (inv a.1), inv (inv a.2)) = _
  rw [inv_twice, inv_twice]

omit [DecidableEq K] in
theorem turn_iterate_four_mul (n : Nat) (a : Carrier K) :
    turn^[4*n] a =
      ((a.1.1, a.1.2+2*(n : K)*a.1.1), (a.2.1, a.2.2+2*(n : K)*a.2.1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (4*n) 4, Function.iterate_add_apply, ih, turn_four]
    ext <;> simp only [Nat.cast_add, Nat.cast_one] <;> ring

theorem division_quasigroup (h3 : (3 : K) ≠ 0) :
    IsQuasigroup (division (K := K)) := by
  constructor
  · intro a
    exact ⟨division_left_injective h3 a, fun b =>
      ⟨division.op (unturn b) a, (division_cross h3 (unturn b) a).trans (turn_unturn b)⟩⟩
  · intro b
    constructor
    · intro a c h
      change division.op a b = division.op c b at h
      apply Function.LeftInverse.injective unturn_turn
      rw [← division_cross h3 a b, ← division_cross h3 c b, h]
    · intro a
      exact ⟨division.op (unturn b) (unturn a), by
        simpa only [turn_unturn] using division_cross_twice h3 (unturn b) (unturn a)⟩

theorem source_quasigroup (h3 : (3 : K) ≠ 0) :
    IsQuasigroup (source (K := K)) :=
  Parastrophes.division_quasigroup (division_quasigroup h3) (isDivision h3)

end Central

section Finite
variable (p : Nat) [Fact p.Prime]

/-- This point already witnesses unbounded row periods. -/
def witness : Carrier (ZMod p) := ((1,0),(0,0))

theorem period_forces_divisibility (n : Nat)
    (h : turn^[n] (witness p) = witness p) : p ∣ 2*n := by
  have h4 : turn^[4*n] (witness p) = witness p := by
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed h 4
  rw [turn_iterate_four_mul] at h4
  have hc := congrArg (fun a : Carrier (ZMod p) => a.1.2) h4
  have hz : ((2*n : Nat) : ZMod p) = 0 := by simpa [witness] using hc
  exact (ZMod.natCast_eq_zero_iff _ _).mp hz

theorem turn_period (a : Carrier (ZMod p)) : turn^[4*p] a = a := by
  rw [turn_iterate_four_mul]
  simp

theorem turn_period_iff (h2 : (2 : ZMod p) ≠ 0) (n : Nat) :
    turn^[n] (witness p) = witness p ↔ 4*p ∣ n := by
  constructor
  · intro h
    have hrem : n % 4 = 0 := by
      have hh := h
      conv_lhs at hh => rw [← Nat.mod_add_div n 4]
      rw [Nat.add_comm, Function.iterate_add_apply, turn_iterate_four_mul] at hh
      have hx := congrArg (fun a : Carrier (ZMod p) => a.1.1) hh
      have hc : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases hc with hr | hr | hr | hr
      · exact hr
      · simp [hr, turn, witness] at hx
      · simp only [hr] at hx
        change (-1 : ZMod p) = 1 at hx
        exact False.elim (h2 (by linear_combination -hx))
      · simp [hr, Function.iterate_succ_apply, turn, inv, witness] at hx
    have hn : 4 * (n / 4) = n := by omega
    have hq : p ∣ n / 4 := by
      rw [← hn, turn_iterate_four_mul] at h
      have hz := congrArg (fun a : Carrier (ZMod p) => a.1.2) h
      have hz' : ((2*(n/4) : Nat) : ZMod p) = 0 := by simpa [witness] using hz
      have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz'
      rcases (Fact.out : p.Prime).dvd_mul.mp hd with hp2 | hq
      · exact False.elim (h2 ((ZMod.natCast_eq_zero_iff 2 p).mpr hp2))
      · exact hq
    obtain ⟨k,hk⟩ := hq
    refine ⟨k, ?_⟩
    calc n = 4*(n/4) := hn.symm
         _ = (4*p)*k := by rw [hk]; ring
  · rintro ⟨k,rfl⟩
    rw [Function.iterate_mul]
    exact Function.iterate_fixed (turn_period p (witness p)) k

theorem cardinality : Fintype.card (Carrier (ZMod p)) = p^4 := by
  simp only [Carrier, Point, Fintype.card_prod, ZMod.card]
  ring

end Finite

/-- There is no fixed positive exponent making all division rows of all finite
E1496 models the identity. This is weaker than failure of uniform term recovery:
a recovering term may use several rows and arbitrary nesting. -/
theorem no_uniform_division_row_period (n : Nat) (hn : 0 < n) :
    ∃ (G : Type) (_ : Fintype G) (M D : Magma G) (e a : G),
      @Equation1496 G M ∧ IsDivision .left M D ∧ (D.op e)^[n] a ≠ a := by
  classical
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (2*n+5)
  letI : Fact p.Prime := ⟨hprime⟩
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega
  refine ⟨Carrier (ZMod p), inferInstance, source, division, ((0,0),(0,0)),
    witness p, source_law1496 h3, division_symm (isDivision h3), ?_⟩
  have he : division.op (((0,0),(0,0)) : Carrier (ZMod p)) = turn := by
    funext a
    exact zero_division a
  rw [he]
  intro h
  have hd := period_forces_divisibility p n h
  have := Nat.le_of_dvd (by omega : 0 < 2*n) hd
  omega

end Parastrophes.CrossInverseLoops
