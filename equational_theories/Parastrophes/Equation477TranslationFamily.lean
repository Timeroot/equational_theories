import equational_theories.Parastrophes.Equation477Image
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Arbitrary periods in the cubic map of E477 division images

Over an abelian group G, use two copies A and B and a parameter k:

    A(x)*A(y) = B(y-x),    A(x)*B(y) = A(x+k-y),
    B(x)*A(y) = A(x+y),    B(x)*B(y) = B(-x-y).

This is an actual E477 left-division image. Its cubic map c(x)=x*(x*x)
acts by translation by k on A and fixes B. Thus even finite images admit
unbounded cubic-map periods; an inverse cannot be recovered by choosing
one fixed positive power of c. This does not rule out other inverse terms
or a single defining equation for the image.
-/
namespace Parastrophes.Eq477Image.TranslationFamily

variable {G : Type} [AddCommGroup G]

@[implicit_reducible] def division (k : G) : Magma (Bool × G) :=
  ⟨fun x y => match x.1, y.1 with
    | false, false => (true, y.2-x.2)
    | false, true => (false, x.2+k-y.2)
    | true, false => (false, x.2+y.2)
    | true, true => (true, -x.2-y.2)⟩

@[implicit_reducible] def source (k : G) : Magma (Bool × G) :=
  ⟨fun x y => match x.1, y.1 with
    | false, false => (true, x.2+k-y.2)
    | false, true => (false, x.2+y.2)
    | true, false => (false, y.2-x.2)
    | true, true => (true, -x.2-y.2)⟩

theorem isDivision (k : G) : IsDivision .left (source k) (division k) := by
  constructor <;> rintro ⟨i,x⟩ ⟨j,y⟩ <;> cases i <;> cases j <;>
    dsimp only [source, division, Magma.op] <;> congr 1 <;> module

theorem core_false (k x : G) : core (division k) (false,x) = (false,x+k) := by
  change (false, x+k-(x-x)) = _
  simp

theorem core_true (k x : G) : core (division k) (true,x) = (true,x) := by
  change (true, -x-(-x-x)) = _
  congr 1
  abel

theorem basis (k : G) : Basis (division k) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨i,x⟩
    cases i <;> change _ = (division k).op _ ((division k).op _ (core (division k) _))
    · rw [core_false]
      dsimp only [division, Magma.op]
      congr 1
      abel
    · rw [core_true]
      dsimp only [division, Magma.op]
      congr 1
      abel
  · have cross (x y : Bool × G) :
        (division k).op x ((division k).op y x) = core (division k) y := by
      rcases x with ⟨i,x⟩
      rcases y with ⟨j,y⟩
      cases i <;> cases j <;> dsimp only [core, division, Magma.op] <;>
        congr 1 <;> module
    intro x y z
    exact (cross x y).trans (cross z y).symm

theorem source_law (k : G) : @Equation477 (Bool × G) (source k) :=
  backward (source k) (division k) (isDivision k) (basis k)

theorem inImage (k : G) : InImage Law477 .left (division k) :=
  ⟨source k, (@Law477.models_iff (Bool × G) (source k)).mpr (source_law k), isDivision k⟩

theorem core_iterate_false (k x : G) (n : ℕ) :
    (core (division k))^[n] (false,x) = (false,x+n • k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, core_false, succ_nsmul]
    congr 1
    abel

/-- Already one countable image has an infinite cubic-map orbit. -/
theorem infinite_orbit (n : ℕ) :
    (core (division (1 : ℤ)))^[n] (false,0) = (false,(n : ℤ)) := by
  rw [core_iterate_false]
  simp

/-- For each positive proposed period n, the image on 2(n+1) elements refutes it. -/
theorem no_uniform_finite_period (n : ℕ) (hn : 0 < n) :
    ∃ (A : Type) (_ : Finite A) (D : Magma A),
      InImage Law477 .left D ∧ ∃ x, (core D)^[n] x ≠ x := by
  letI : NeZero (n+1) := ⟨by omega⟩
  refine ⟨Bool × ZMod (n+1), inferInstance, division 1, inImage 1, (false,0), ?_⟩
  rw [core_iterate_false]
  simp only [nsmul_eq_mul, mul_one, zero_add]
  intro he
  have hd : n+1 ∣ n := (ZMod.natCast_eq_zero_iff n (n+1)).mp (congrArg Prod.snd he)
  have := Nat.le_of_dvd hn hd
  omega

end Parastrophes.Eq477Image.TranslationFamily
