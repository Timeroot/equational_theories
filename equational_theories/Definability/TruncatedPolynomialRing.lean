import equational_theories.Definability.MatrixFamilyCounting
import Mathlib.Algebra.Group.TransferInstance

/-! Small truncated polynomial rings, with coefficient-vector arithmetic.
All ring identities are checked algebraically over an arbitrary commutative ring. -/

namespace Magma.TruncatedPolynomial

@[ext] structure T (R : Type) (d : ℕ) where
  coeff : Fin d → R
  deriving DecidableEq, Inhabited

variable {R : Type} [CommRing R] {d : ℕ}

def coeffEquiv : T R d ≃ (Fin d → R) where
  toFun := T.coeff
  invFun := T.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance [Fintype R] : Fintype (T R d) := Fintype.ofEquiv (Fin d → R) coeffEquiv.symm

instance : AddCommGroup (T R d) := coeffEquiv.addCommGroup

def scalar (r : R) : T R d := ⟨fun i => if i.val = 0 then r else 0⟩
instance : One (T R d) := ⟨scalar 1⟩
instance : NatCast (T R d) := ⟨fun n => scalar n⟩
instance : IntCast (T R d) := ⟨fun n => scalar n⟩

@[simp] theorem zero_coeff (i : Fin d) : (0 : T R d).coeff i = 0 := rfl
@[simp] theorem add_coeff (x y : T R d) (i : Fin d) :
    (x + y).coeff i = x.coeff i + y.coeff i := rfl
@[simp] theorem neg_coeff (x : T R d) (i : Fin d) :
    (-x).coeff i = -x.coeff i := rfl
@[simp] theorem sub_coeff (x y : T R d) (i : Fin d) :
    (x - y).coeff i = x.coeff i - y.coeff i := rfl
@[simp] theorem one_coeff (i : Fin d) :
    (1 : T R d).coeff i = if i.val = 0 then 1 else 0 := rfl
@[simp] theorem natCast_coeff (n : ℕ) (i : Fin d) :
    (n : T R d).coeff i = if i.val = 0 then (n : R) else 0 := rfl
@[simp] theorem intCast_coeff (n : ℤ) (i : Fin d) :
    (n : T R d).coeff i = if i.val = 0 then (n : R) else 0 := rfl

def mul3 (x y : T R 3) : T R 3 := ⟨![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0]⟩
def mul3Cached (x y : T R 3) : T R 3 :=
  let coeffs := Vector.ofFn (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0] : Fin 3 → R)
  ⟨fun i => coeffs.get i⟩
@[csimp] theorem mul3_eq_cached : @mul3 = @mul3Cached := by
  funext R inst x y
  ext i
  simp [mul3, mul3Cached, Vector.get]


instance : Mul (T R 3) := ⟨mul3⟩
@[simp] theorem mul3_coeff (x y : T R 3) (i : Fin 3) :
    (x * y).coeff i = (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0] : Fin 3 → R) i := rfl

instance : CommRing (T R 3) where
  __ := (inferInstance : AddCommGroup (T R 3))
  __ := (inferInstance : One (T R 3))
  __ := (inferInstance : Mul (T R 3))
  __ := (inferInstance : NatCast (T R 3))
  __ := (inferInstance : IntCast (T R 3))
  npow := npowRec
  mul_assoc := by intros; ext i; fin_cases i <;> simp <;> ring
  one_mul := by intros; ext i; fin_cases i <;> simp
  mul_one := by intros; ext i; fin_cases i <;> simp
  mul_comm := by intros; ext i; fin_cases i <;> simp <;> ring
  left_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  right_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  zero_mul := by intros; ext i; fin_cases i <;> simp
  mul_zero := by intros; ext i; fin_cases i <;> simp
  natCast_zero := by ext i; fin_cases i <;> simp
  natCast_succ := by intros; ext i; fin_cases i <;> simp
  intCast_ofNat := by intros; ext i; fin_cases i <;> simp
  intCast_negSucc := by intros; ext i; fin_cases i <;> simp

def mul4 (x y : T R 4) : T R 4 := ⟨![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0]⟩
def mul4Cached (x y : T R 4) : T R 4 :=
  let coeffs := Vector.ofFn (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0] : Fin 4 → R)
  ⟨fun i => coeffs.get i⟩
@[csimp] theorem mul4_eq_cached : @mul4 = @mul4Cached := by
  funext R inst x y
  ext i
  simp [mul4, mul4Cached, Vector.get]


instance : Mul (T R 4) := ⟨mul4⟩
@[simp] theorem mul4_coeff (x y : T R 4) (i : Fin 4) :
    (x * y).coeff i = (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0] : Fin 4 → R) i := rfl

instance : CommRing (T R 4) where
  __ := (inferInstance : AddCommGroup (T R 4))
  __ := (inferInstance : One (T R 4))
  __ := (inferInstance : Mul (T R 4))
  __ := (inferInstance : NatCast (T R 4))
  __ := (inferInstance : IntCast (T R 4))
  npow := npowRec
  mul_assoc := by intros; ext i; fin_cases i <;> simp <;> ring
  one_mul := by intros; ext i; fin_cases i <;> simp
  mul_one := by intros; ext i; fin_cases i <;> simp
  mul_comm := by intros; ext i; fin_cases i <;> simp <;> ring
  left_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  right_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  zero_mul := by intros; ext i; fin_cases i <;> simp
  mul_zero := by intros; ext i; fin_cases i <;> simp
  natCast_zero := by ext i; fin_cases i <;> simp
  natCast_succ := by intros; ext i; fin_cases i <;> simp
  intCast_ofNat := by intros; ext i; fin_cases i <;> simp
  intCast_negSucc := by intros; ext i; fin_cases i <;> simp

def mul5 (x y : T R 5) : T R 5 := ⟨![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0, x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 + x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0]⟩
def mul5Cached (x y : T R 5) : T R 5 :=
  let coeffs := Vector.ofFn (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0, x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 + x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0] : Fin 5 → R)
  ⟨fun i => coeffs.get i⟩
@[csimp] theorem mul5_eq_cached : @mul5 = @mul5Cached := by
  funext R inst x y
  ext i
  simp [mul5, mul5Cached, Vector.get]


instance : Mul (T R 5) := ⟨mul5⟩
@[simp] theorem mul5_coeff (x y : T R 5) (i : Fin 5) :
    (x * y).coeff i = (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0, x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 + x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0] : Fin 5 → R) i := rfl

instance : CommRing (T R 5) where
  __ := (inferInstance : AddCommGroup (T R 5))
  __ := (inferInstance : One (T R 5))
  __ := (inferInstance : Mul (T R 5))
  __ := (inferInstance : NatCast (T R 5))
  __ := (inferInstance : IntCast (T R 5))
  npow := npowRec
  mul_assoc := by intros; ext i; fin_cases i <;> simp <;> ring
  one_mul := by intros; ext i; fin_cases i <;> simp
  mul_one := by intros; ext i; fin_cases i <;> simp
  mul_comm := by intros; ext i; fin_cases i <;> simp <;> ring
  left_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  right_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  zero_mul := by intros; ext i; fin_cases i <;> simp
  mul_zero := by intros; ext i; fin_cases i <;> simp
  natCast_zero := by ext i; fin_cases i <;> simp
  natCast_succ := by intros; ext i; fin_cases i <;> simp
  intCast_ofNat := by intros; ext i; fin_cases i <;> simp
  intCast_negSucc := by intros; ext i; fin_cases i <;> simp

def mul6 (x y : T R 6) : T R 6 := ⟨![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0, x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 + x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0, x.coeff 0 * y.coeff 5 + x.coeff 1 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 3 * y.coeff 2 + x.coeff 4 * y.coeff 1 + x.coeff 5 * y.coeff 0]⟩
def mul6Cached (x y : T R 6) : T R 6 :=
  let coeffs := Vector.ofFn (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0, x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 + x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0, x.coeff 0 * y.coeff 5 + x.coeff 1 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 3 * y.coeff 2 + x.coeff 4 * y.coeff 1 + x.coeff 5 * y.coeff 0] : Fin 6 → R)
  ⟨fun i => coeffs.get i⟩
@[csimp] theorem mul6_eq_cached : @mul6 = @mul6Cached := by
  funext R inst x y
  ext i
  simp [mul6, mul6Cached, Vector.get]


instance : Mul (T R 6) := ⟨mul6⟩
@[simp] theorem mul6_coeff (x y : T R 6) (i : Fin 6) :
    (x * y).coeff i = (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0, x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 + x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0, x.coeff 0 * y.coeff 5 + x.coeff 1 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 3 * y.coeff 2 + x.coeff 4 * y.coeff 1 + x.coeff 5 * y.coeff 0] : Fin 6 → R) i := rfl

instance : CommRing (T R 6) where
  __ := (inferInstance : AddCommGroup (T R 6))
  __ := (inferInstance : One (T R 6))
  __ := (inferInstance : Mul (T R 6))
  __ := (inferInstance : NatCast (T R 6))
  __ := (inferInstance : IntCast (T R 6))
  npow := npowRec
  mul_assoc := by intros; ext i; fin_cases i <;> simp <;> ring
  one_mul := by intros; ext i; fin_cases i <;> simp
  mul_one := by intros; ext i; fin_cases i <;> simp
  mul_comm := by intros; ext i; fin_cases i <;> simp <;> ring
  left_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  right_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  zero_mul := by intros; ext i; fin_cases i <;> simp
  mul_zero := by intros; ext i; fin_cases i <;> simp
  natCast_zero := by ext i; fin_cases i <;> simp
  natCast_succ := by intros; ext i; fin_cases i <;> simp
  intCast_ofNat := by intros; ext i; fin_cases i <;> simp
  intCast_negSucc := by intros; ext i; fin_cases i <;> simp

def mul8 (x y : T R 8) : T R 8 := ⟨![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0, x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 + x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0, x.coeff 0 * y.coeff 5 + x.coeff 1 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 3 * y.coeff 2 + x.coeff 4 * y.coeff 1 + x.coeff 5 * y.coeff 0, x.coeff 0 * y.coeff 6 + x.coeff 1 * y.coeff 5 + x.coeff 2 * y.coeff 4 + x.coeff 3 * y.coeff 3 + x.coeff 4 * y.coeff 2 + x.coeff 5 * y.coeff 1 + x.coeff 6 * y.coeff 0, x.coeff 0 * y.coeff 7 + x.coeff 1 * y.coeff 6 + x.coeff 2 * y.coeff 5 + x.coeff 3 * y.coeff 4 + x.coeff 4 * y.coeff 3 + x.coeff 5 * y.coeff 2 + x.coeff 6 * y.coeff 1 + x.coeff 7 * y.coeff 0]⟩
def mul8Cached (x y : T R 8) : T R 8 :=
  let coeffs := Vector.ofFn (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0, x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 + x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0, x.coeff 0 * y.coeff 5 + x.coeff 1 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 3 * y.coeff 2 + x.coeff 4 * y.coeff 1 + x.coeff 5 * y.coeff 0, x.coeff 0 * y.coeff 6 + x.coeff 1 * y.coeff 5 + x.coeff 2 * y.coeff 4 + x.coeff 3 * y.coeff 3 + x.coeff 4 * y.coeff 2 + x.coeff 5 * y.coeff 1 + x.coeff 6 * y.coeff 0, x.coeff 0 * y.coeff 7 + x.coeff 1 * y.coeff 6 + x.coeff 2 * y.coeff 5 + x.coeff 3 * y.coeff 4 + x.coeff 4 * y.coeff 3 + x.coeff 5 * y.coeff 2 + x.coeff 6 * y.coeff 1 + x.coeff 7 * y.coeff 0] : Fin 8 → R)
  ⟨fun i => coeffs.get i⟩
@[csimp] theorem mul8_eq_cached : @mul8 = @mul8Cached := by
  funext R inst x y
  ext i
  simp [mul8, mul8Cached, Vector.get]


instance : Mul (T R 8) := ⟨mul8⟩
@[simp] theorem mul8_coeff (x y : T R 8) (i : Fin 8) :
    (x * y).coeff i = (![x.coeff 0 * y.coeff 0, x.coeff 0 * y.coeff 1 + x.coeff 1 * y.coeff 0, x.coeff 0 * y.coeff 2 + x.coeff 1 * y.coeff 1 + x.coeff 2 * y.coeff 0, x.coeff 0 * y.coeff 3 + x.coeff 1 * y.coeff 2 + x.coeff 2 * y.coeff 1 + x.coeff 3 * y.coeff 0, x.coeff 0 * y.coeff 4 + x.coeff 1 * y.coeff 3 + x.coeff 2 * y.coeff 2 + x.coeff 3 * y.coeff 1 + x.coeff 4 * y.coeff 0, x.coeff 0 * y.coeff 5 + x.coeff 1 * y.coeff 4 + x.coeff 2 * y.coeff 3 + x.coeff 3 * y.coeff 2 + x.coeff 4 * y.coeff 1 + x.coeff 5 * y.coeff 0, x.coeff 0 * y.coeff 6 + x.coeff 1 * y.coeff 5 + x.coeff 2 * y.coeff 4 + x.coeff 3 * y.coeff 3 + x.coeff 4 * y.coeff 2 + x.coeff 5 * y.coeff 1 + x.coeff 6 * y.coeff 0, x.coeff 0 * y.coeff 7 + x.coeff 1 * y.coeff 6 + x.coeff 2 * y.coeff 5 + x.coeff 3 * y.coeff 4 + x.coeff 4 * y.coeff 3 + x.coeff 5 * y.coeff 2 + x.coeff 6 * y.coeff 1 + x.coeff 7 * y.coeff 0] : Fin 8 → R) i := rfl

instance : CommRing (T R 8) where
  __ := (inferInstance : AddCommGroup (T R 8))
  __ := (inferInstance : One (T R 8))
  __ := (inferInstance : Mul (T R 8))
  __ := (inferInstance : NatCast (T R 8))
  __ := (inferInstance : IntCast (T R 8))
  npow := npowRec
  mul_assoc := by intros; ext i; fin_cases i <;> simp <;> ring
  one_mul := by intros; ext i; fin_cases i <;> simp
  mul_one := by intros; ext i; fin_cases i <;> simp
  mul_comm := by intros; ext i; fin_cases i <;> simp <;> ring
  left_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  right_distrib := by intros; ext i; fin_cases i <;> simp <;> ring
  zero_mul := by intros; ext i; fin_cases i <;> simp
  mul_zero := by intros; ext i; fin_cases i <;> simp
  natCast_zero := by ext i; fin_cases i <;> simp
  natCast_succ := by intros; ext i; fin_cases i <;> simp
  intCast_ofNat := by intros; ext i; fin_cases i <;> simp
  intCast_negSucc := by intros; ext i; fin_cases i <;> simp

end Magma.TruncatedPolynomial
