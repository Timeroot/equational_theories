import equational_theories.Parastrophes.CrossInverseLoopExtensions
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic

/-!
# Inverse periods in central extensions

Two inverse steps add the difference of two diagonal offsets. Summing those
differences over an even base cycle gives its fibre displacement. The exact
period upstairs is the base period multiplied by the additive order of that
displacement. This avoids enumerating the enlarged loop.

The general existence of offsets for the towers in
`docs/cross-inverse-loop-towers.md` is a separate, as yet unformalized argument.
No image-characterization result is asserted or registered here.
-/

namespace Parastrophes.CrossInverseLoopExtensions.CIPLoop
open Function

variable {A : Type} (Q : CIPLoop A)

/-- Rotate a multiplication triple, keeping its first two coordinates. -/
def pairTurn (p : A × A) : A × A := (Q.magma.op p.1 p.2, Q.inverse p.1)

theorem pairTurn_twice (x y : A) :
    Q.pairTurn (Q.pairTurn (x,y)) = (y, Q.inverse (Q.magma.op x y)) := by
  exact Prod.ext (Q.cross x y) rfl

/-- This identity reduces offset consistency to inverse cycles in the base. -/
theorem pairTurn_three (x y : A) :
    Q.pairTurn (Q.pairTurn (Q.pairTurn (x,y))) = (Q.inverse x, Q.inverse y) := by
  rw [Q.pairTurn_twice x y]
  apply Prod.ext
  · change Q.magma.op y (Q.inverse (Q.magma.op x y)) = Q.inverse x
    have h := Q.cross (Q.magma.op x y) (Q.inverse x)
    rwa [Q.cross x y] at h
  · rfl

variable {K : Type} [AddCommGroup K] (c : Q.Offset K)

def diagonalOffset (x : A) : K := c.value x (Q.inverse x)

def pairDisplacement (x : A) : K :=
  Q.diagonalOffset c x - Q.diagonalOffset c (Q.inverse x)

theorem liftInverse_twice (x : A) (u : K) :
    Q.liftInverse c (Q.liftInverse c (x,u)) =
      (Q.inverse (Q.inverse x), u + Q.pairDisplacement c x) := by
  apply Prod.ext
  · rfl
  · change -(-u - c.value x (Q.inverse x)) -
      c.value (Q.inverse x) (Q.inverse (Q.inverse x)) =
        u + (c.value x (Q.inverse x) -
          c.value (Q.inverse x) (Q.inverse (Q.inverse x)))
    abel

/-- The alternating trace over `2*k` steps, grouped into adjacent pairs. -/
def evenTrace (x : A) : Nat → K
  | 0 => 0
  | k + 1 => evenTrace x k +
      Q.pairDisplacement c ((Q.inverse : A → A)^[2*k] x)

theorem liftInverse_even (k : Nat) (x : A) (u : K) :
    ((Q.liftInverse c : A × K → A × K)^[2*k]) (x,u) =
      ((Q.inverse : A → A)^[2*k] x, u + Q.evenTrace c x k) := by
  induction k with
  | zero => simp [evenTrace]
  | succ k ih =>
    have hn : 2 * (k + 1) = 2 + 2*k := by omega
    rw [hn, iterate_add_apply, ih]
    change Q.liftInverse c (Q.liftInverse c _) = _
    rw [Q.liftInverse_twice, iterate_add_apply]
    apply Prod.ext
    · rfl
    · simp only [evenTrace]
      abel

theorem liftInverse_fst (n : Nat) (z : A × K) :
    (((Q.liftInverse c : A × K → A × K)^[n]) z).1 =
      (Q.inverse : A → A)^[n] z.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact congrArg Q.inverse ih

/-- Once the base returns, each circuit adds the same displacement. -/
theorem liftInverse_circuits (k m : Nat) (x : A) (u : K)
    (hx : (Q.inverse : A → A)^[2*k] x = x) :
    ((Q.liftInverse c : A × K → A × K)^[2*k*m]) (x,u) =
      (x, u + m • Q.evenTrace c x k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Nat.add_comm, iterate_add_apply, ih, Q.liftInverse_even, hx]
    apply Prod.ext
    · rfl
    · rw [succ_nsmul]
      abel_nf

/-- The base period times the additive order of its trace is the exact period
of every point in that fibre. No finiteness of either carrier is required. -/
theorem liftInverse_minimalPeriod (k : Nat) (x : A) (u : K)
    (hx : minimalPeriod (Q.inverse : A → A) x = 2*k) :
    minimalPeriod (Q.liftInverse c : A × K → A × K) (x,u) =
      2*k * addOrderOf (Q.evenTrace c x k) := by
  have hbase : (Q.inverse : A → A)^[2*k] x = x := by
    rw [← hx]
    exact isPeriodicPt_minimalPeriod _ _
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    change ((Q.liftInverse c : A × K → A × K)^[_]) (x,u) = (x,u)
    rw [Q.liftInverse_circuits c k _ x u hbase, addOrderOf_nsmul_eq_zero, add_zero]
  · let n := minimalPeriod (Q.liftInverse c : A × K → A × K) (x,u)
    have hn : ((Q.liftInverse c : A × K → A × K)^[n]) (x,u) = (x,u) :=
      isPeriodicPt_minimalPeriod _ _
    have hb : IsPeriodicPt (Q.inverse : A → A) n x := by
      have he := congrArg Prod.fst hn
      rwa [Q.liftInverse_fst] at he
    have hd : 2*k ∣ n := by simpa only [hx] using hb.minimalPeriod_dvd
    obtain ⟨m, hm⟩ := hd
    have hs : m • Q.evenTrace c x k = 0 := by
      rw [hm, Q.liftInverse_circuits c k m x u hbase] at hn
      have he := congrArg Prod.snd hn
      exact add_left_cancel (he.trans (add_zero u).symm)
    have ho : addOrderOf (Q.evenTrace c x k) ∣ m :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hs
    change 2*k * addOrderOf (Q.evenTrace c x k) ∣ n
    rw [hm]
    exact Nat.mul_dvd_mul_left _ ho

/-- A nonzero trace in the prime field multiplies the exact period by `p`.
Only the trace on the smaller base must be checked. -/
theorem liftInverse_minimalPeriod_prime {p : Nat} [Fact p.Prime]
    (c : Q.Offset (ZMod p)) (k : Nat) (x : A) (u : ZMod p)
    (hx : minimalPeriod (Q.inverse : A → A) x = 2*k)
    (ht : Q.evenTrace c x k ≠ 0) :
    minimalPeriod (Q.liftInverse c : A × ZMod p → A × ZMod p) (x,u) = 2*k*p := by
  rw [Q.liftInverse_minimalPeriod c k x u hx]
  congr 1
  apply addOrderOf_eq_prime _ ht
  simp [nsmul_eq_mul]

end Parastrophes.CrossInverseLoopExtensions.CIPLoop
