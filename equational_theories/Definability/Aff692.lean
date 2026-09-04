import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.DeriveFintype
import equational_theories.Definability.AffineClone

/-!
# The fixed-point-free affine model of 692, and the eight targets it kills

Equation 692 is `x = y ◇ (x ◇ ((z ◇ y) ◇ z))`. Vampire proves from it alone that
`B x := x ◇ (x ◇ x)` is an automorphism with `B³ = id` and `y ◇ (x ◇ y) = B x`, and that a single
fixed point of `B` forces `B = id`, i.e. equation 14. So every 692-model is either a 14-model or
one on which `B` is fixed-point free, and `Definability/Shift692.lean` already carries a nine
element example of the second kind. That one is not enough: its clone is all `81` affine maps of
`(ℤ/3)²`, and among them are maps satisfying 14.

The affine models are easy to classify. Over a commutative ring `R`, `x ◇ y = α x + β y + k`
satisfies 692 exactly when

    α β = 1,    β³ = -1,    (β + 1)² k = 0,

and then `B x = x + (β + 1) k`, so `B = id` iff `t := (β + 1) k` vanishes. By
`Definability/AffineClone.lean` the clone of such a magma is contained in

    □(x, y) = (1 - q + r s) x + q y + r k,    s := α + β - 1,

and a member satisfies 14 iff `q³ = -1`, `r s = -(q² - q + 1)` and `(q + 1) r k = 0`. Taking
`q = -1` makes the last condition vacuous, so a refuting ring must in particular have no `r` with
`r s = -3` — which rules out every `ℤ/m`, and explains why all the cyclic affine 692-models have
14 in their clones. It also rules out characteristic three (there `s = -(β+1)²` and `r = 0` works)
and every ring in which `β³ + 1` factors coprimely, since then `q` can be chosen componentwise.

An exhaustive scan of `ℤ/m[β]/(β³ + 1)` finds the first survivor at `m = 9`, and quotienting by the
smallest ideal that keeps it survivable leaves

    R₈₁ = (ℤ/9)[u] / (u³, 3u),    β = u - 1,    α = -β² ,    k = u² - u,

an eighty-one element local ring with `t = -u² ≠ 0`. Its clone coset has `6561` members and none of
them satisfies any of eleven laws, eight of which are open against the sources below. Note what
the constant buys: `β³ = -1` needs a cube root of `-1` other than `-1` itself, and `3u = 0` with
`u³ = 0` is exactly what stops `r s = -3` from being solvable — `r (3 + u²) = 3 a + a u²` can never
equal `3`.

The certificate is two `native_decide` sweeps per source law (`81²` pairs) and one per target
(`6561` clone members at three or four instances), the instances being the all-zero assignment and
the unit vectors, which between them recover the full coefficient condition.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- `R₈₁ = (ℤ/9)[u] / (u³, 3u)`, in the basis `1, u, u²`. Because `3u = 0` the two upper
coordinates live in `ℤ/3`, so the additive group is `ℤ/9 ⊕ ℤ/3 ⊕ ℤ/3`. -/
@[ext] structure R81 where
  /-- the constant coefficient -/
  a : ZMod 9
  /-- the coefficient of `u` -/
  b : ZMod 3
  /-- the coefficient of `u²` -/
  c : ZMod 3
deriving DecidableEq, Fintype

namespace R81

/-- Reduction mod three: the only place the two moduli meet. -/
def red : ZMod 9 →+* ZMod 3 := ZMod.castHom (by norm_num) (ZMod 3)

instance : Zero R81 := ⟨⟨0, 0, 0⟩⟩
instance : One R81 := ⟨⟨1, 0, 0⟩⟩
instance : Add R81 := ⟨fun x y ↦ ⟨x.a + y.a, x.b + y.b, x.c + y.c⟩⟩
instance : Neg R81 := ⟨fun x ↦ ⟨-x.a, -x.b, -x.c⟩⟩
instance : Sub R81 := ⟨fun x y ↦ ⟨x.a - y.a, x.b - y.b, x.c - y.c⟩⟩
instance : Mul R81 := ⟨fun x y ↦ ⟨x.a * y.a, red x.a * y.b + x.b * red y.a,
                                  red x.a * y.c + x.b * y.b + x.c * red y.a⟩⟩

@[simp] theorem zero_a : (0 : R81).a = 0 := rfl
@[simp] theorem zero_b : (0 : R81).b = 0 := rfl
@[simp] theorem zero_c : (0 : R81).c = 0 := rfl
@[simp] theorem one_a : (1 : R81).a = 1 := rfl
@[simp] theorem one_b : (1 : R81).b = 0 := rfl
@[simp] theorem one_c : (1 : R81).c = 0 := rfl
@[simp] theorem add_a (x y : R81) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : R81) : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c (x y : R81) : (x + y).c = x.c + y.c := rfl
@[simp] theorem neg_a (x : R81) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : R81) : (-x).b = -x.b := rfl
@[simp] theorem neg_c (x : R81) : (-x).c = -x.c := rfl
@[simp] theorem sub_a (x y : R81) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : R81) : (x - y).b = x.b - y.b := rfl
@[simp] theorem sub_c (x y : R81) : (x - y).c = x.c - y.c := rfl
@[simp] theorem mul_a (x y : R81) : (x * y).a = x.a * y.a := rfl
@[simp] theorem mul_b (x y : R81) : (x * y).b = red x.a * y.b + x.b * red y.a := rfl
@[simp] theorem mul_c (x y : R81) :
    (x * y).c = red x.a * y.c + x.b * y.b + x.c * red y.a := rfl

instance : CommRing R81 where
  add := (· + ·)
  zero := 0
  one := 1
  neg := (- ·)
  sub := (· - ·)
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg _ _ := by ext <;> simp <;> ring
  add_assoc _ _ _ := by ext <;> simp <;> ring
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  add_comm _ _ := by ext <;> simp <;> ring
  neg_add_cancel _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp [map_mul] <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp
  left_distrib _ _ _ := by ext <;> simp [map_add] <;> ring
  right_distrib _ _ _ := by ext <;> simp [map_add] <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_comm _ _ := by ext <;> simp <;> ring

/-- The nilpotent `u`, with `u³ = 0` and `3u = 0`. -/
def u : R81 := ⟨0, 1, 0⟩

/-- `β = u - 1`, a cube root of `-1` that is not `-1`. -/
def bb : R81 := ⟨8, 1, 0⟩

/-- `α = -β² = β⁻¹`. -/
def aa : R81 := ⟨8, 2, 2⟩

/-- The shift `k = u² - u`. -/
def kk : R81 := ⟨0, 2, 1⟩

theorem u_cube : u * u * u = 0 := by decide
theorem three_u : u + u + u = 0 := by decide
theorem bb_eq : bb = u - 1 := by decide
theorem aa_eq : aa = -(bb * bb) := by decide
theorem kk_eq : kk = u * u - u := by decide

/-- The three conditions for `x ◇ y = α x + β y + k` to satisfy 692. -/
theorem aa_mul_bb : aa * bb = 1 := by decide

theorem bb_cube : bb * bb * bb = -1 := by decide

theorem sq_bb_add_one_mul_kk : (bb + 1) * (bb + 1) * kk = 0 := by decide

/-- `B x = x + (β + 1) k` is fixed-point free: this is the whole point of the model. -/
theorem bb_add_one_mul_kk : (bb + 1) * kk ≠ 0 := by decide

/-- `s = α + β - 1 = -3 - u²`, and there is no `r` with `r s = -3`; that is what stops the clone
member `q = -1` from satisfying equation 14. -/
theorem s_eq : aa + bb - 1 = -3 - u * u := by decide

theorem no_inverse_s : ∀ r : R81, r * (aa + bb - 1) ≠ -3 := by decide

end R81

/-- The model `x ◇ y = α x + β y + k` over `R₈₁`. -/
@[implicit_reducible]
def aff692 : Magma R81 := Magma.aff R81.aa R81.bb R81.kk

/-- Its clone coset, indexed by a pair `(q, r)` of ring elements. -/
@[implicit_reducible]
def aff692Fam (q r : R81) : Magma R81 := Magma.affFam R81.aa R81.bb R81.kk q r

/-- The same member as a bare operation. The coverage sweeps below are quantified over `q` and `r`
and read more easily without the projection. -/
abbrev aff692op (q r : R81) : R81 → R81 → R81 := (aff692Fam q r).op


/-! ### The model satisfies each source law -/

/-- `x = y ◇ (x ◇ ((z ◇ y) ◇ z))` -/
theorem aff692_sat692 : @Equation692 R81 aff692 := by native_decide


/-! ### No member of the clone satisfies any of the eight targets

A law with `k` variables holds of the affine map `p x + q y + d` iff the two sides agree
coefficient by coefficient and `(e_lhs - e_rhs) d = 0`, and the `k + 1` instances below --
all variables zero, then each unit vector -- pin down exactly that. So the sweeps are complete,
not merely necessary conditions. -/

/-- `x = y ◇ (x ◇ y)` -/
theorem aff692_cov14 : ∀ q r : R81,
    (0 : R81) = aff692op q r 0 (aff692op q r 0 0) →
    (1 : R81) = aff692op q r 0 (aff692op q r 1 0) →
    (0 : R81) = aff692op q r 1 (aff692op q r 0 1) →
    False := by native_decide

/-- `x = y ◇ (x ◇ (y ◇ (y ◇ y)))` -/
theorem aff692_cov477 : ∀ q r : R81,
    (0 : R81) = aff692op q r 0 (aff692op q r 0 (aff692op q r 0 (aff692op q r 0 0))) →
    (1 : R81) = aff692op q r 0 (aff692op q r 1 (aff692op q r 0 (aff692op q r 0 0))) →
    (0 : R81) = aff692op q r 1 (aff692op q r 0 (aff692op q r 1 (aff692op q r 1 1))) →
    False := by native_decide

/-- `x = y ◇ ((y ◇ (x ◇ y)) ◇ y)` -/
theorem aff692_cov1113 : ∀ q r : R81,
    (0 : R81) = aff692op q r 0 (aff692op q r (aff692op q r 0 (aff692op q r 0 0)) 0) →
    (1 : R81) = aff692op q r 0 (aff692op q r (aff692op q r 0 (aff692op q r 1 0)) 0) →
    (0 : R81) = aff692op q r 1 (aff692op q r (aff692op q r 1 (aff692op q r 0 1)) 1) →
    False := by native_decide

/-- `x = (y ◇ x) ◇ (y ◇ (y ◇ y))` -/
theorem aff692_cov1492 : ∀ q r : R81,
    (0 : R81) = aff692op q r (aff692op q r 0 0) (aff692op q r 0 (aff692op q r 0 0)) →
    (1 : R81) = aff692op q r (aff692op q r 0 1) (aff692op q r 0 (aff692op q r 0 0)) →
    (0 : R81) = aff692op q r (aff692op q r 1 0) (aff692op q r 1 (aff692op q r 1 1)) →
    False := by native_decide

/-- `x = (y ◇ y) ◇ (x ◇ (y ◇ y))` -/
theorem aff692_cov1519 : ∀ q r : R81,
    (0 : R81) = aff692op q r (aff692op q r 0 0) (aff692op q r 0 (aff692op q r 0 0)) →
    (1 : R81) = aff692op q r (aff692op q r 0 0) (aff692op q r 1 (aff692op q r 0 0)) →
    (0 : R81) = aff692op q r (aff692op q r 1 1) (aff692op q r 0 (aff692op q r 1 1)) →
    False := by native_decide

/-- `x ◇ x = y ◇ (x ◇ (y ◇ y))` -/
theorem aff692_cov3272 : ∀ q r : R81,
    aff692op q r 0 0 = aff692op q r 0 (aff692op q r 0 (aff692op q r 0 0)) →
    aff692op q r 1 1 = aff692op q r 0 (aff692op q r 1 (aff692op q r 0 0)) →
    aff692op q r 0 0 = aff692op q r 1 (aff692op q r 0 (aff692op q r 1 1)) →
    False := by native_decide

/-- `x ◇ x = y ◇ ((x ◇ x) ◇ y)` -/
theorem aff692_cov3472 : ∀ q r : R81,
    aff692op q r 0 0 = aff692op q r 0 (aff692op q r (aff692op q r 0 0) 0) →
    aff692op q r 1 1 = aff692op q r 0 (aff692op q r (aff692op q r 1 1) 0) →
    aff692op q r 0 0 = aff692op q r 1 (aff692op q r (aff692op q r 0 0) 1) →
    False := by native_decide

/-- `x ◇ y = z ◇ ((x ◇ y) ◇ z)` -/
theorem aff692_cov3588 : ∀ q r : R81,
    aff692op q r 0 0 = aff692op q r 0 (aff692op q r (aff692op q r 0 0) 0) →
    aff692op q r 1 0 = aff692op q r 0 (aff692op q r (aff692op q r 1 0) 0) →
    aff692op q r 0 1 = aff692op q r 0 (aff692op q r (aff692op q r 0 1) 0) →
    aff692op q r 0 0 = aff692op q r 1 (aff692op q r (aff692op q r 0 0) 1) →
    False := by native_decide


/-! ### The refutations -/

theorem Equation14_not_termDefinableFromFin_Equation692 :
    ¬ Law14.TermDefinableFromFin Law692 :=
  not_termDefinableFromFin_of_aff R81.aa R81.bb R81.kk
    ((@Law692.models_iff R81 aff692).mpr aff692_sat692)
    fun q r hm ↦
      let h := (@Law14.models_iff R81 (aff692Fam q r)).mp hm
      aff692_cov14 q r (h 0 0) (h 1 0) (h 0 1)

theorem Equation477_not_termDefinableFromFin_Equation692 :
    ¬ Law477.TermDefinableFromFin Law692 :=
  not_termDefinableFromFin_of_aff R81.aa R81.bb R81.kk
    ((@Law692.models_iff R81 aff692).mpr aff692_sat692)
    fun q r hm ↦
      let h := (@Law477.models_iff R81 (aff692Fam q r)).mp hm
      aff692_cov477 q r (h 0 0) (h 1 0) (h 0 1)

theorem Equation1113_not_termDefinableFromFin_Equation692 :
    ¬ Law1113.TermDefinableFromFin Law692 :=
  not_termDefinableFromFin_of_aff R81.aa R81.bb R81.kk
    ((@Law692.models_iff R81 aff692).mpr aff692_sat692)
    fun q r hm ↦
      let h := (@Law1113.models_iff R81 (aff692Fam q r)).mp hm
      aff692_cov1113 q r (h 0 0) (h 1 0) (h 0 1)

theorem Equation1492_not_termDefinableFromFin_Equation692 :
    ¬ Law1492.TermDefinableFromFin Law692 :=
  not_termDefinableFromFin_of_aff R81.aa R81.bb R81.kk
    ((@Law692.models_iff R81 aff692).mpr aff692_sat692)
    fun q r hm ↦
      let h := (@Law1492.models_iff R81 (aff692Fam q r)).mp hm
      aff692_cov1492 q r (h 0 0) (h 1 0) (h 0 1)

theorem Equation1519_not_termDefinableFromFin_Equation692 :
    ¬ Law1519.TermDefinableFromFin Law692 :=
  not_termDefinableFromFin_of_aff R81.aa R81.bb R81.kk
    ((@Law692.models_iff R81 aff692).mpr aff692_sat692)
    fun q r hm ↦
      let h := (@Law1519.models_iff R81 (aff692Fam q r)).mp hm
      aff692_cov1519 q r (h 0 0) (h 1 0) (h 0 1)

theorem Equation3272_not_termDefinableFromFin_Equation692 :
    ¬ Law3272.TermDefinableFromFin Law692 :=
  not_termDefinableFromFin_of_aff R81.aa R81.bb R81.kk
    ((@Law692.models_iff R81 aff692).mpr aff692_sat692)
    fun q r hm ↦
      let h := (@Law3272.models_iff R81 (aff692Fam q r)).mp hm
      aff692_cov3272 q r (h 0 0) (h 1 0) (h 0 1)

theorem Equation3472_not_termDefinableFromFin_Equation692 :
    ¬ Law3472.TermDefinableFromFin Law692 :=
  not_termDefinableFromFin_of_aff R81.aa R81.bb R81.kk
    ((@Law692.models_iff R81 aff692).mpr aff692_sat692)
    fun q r hm ↦
      let h := (@Law3472.models_iff R81 (aff692Fam q r)).mp hm
      aff692_cov3472 q r (h 0 0) (h 1 0) (h 0 1)

theorem Equation3588_not_termDefinableFromFin_Equation692 :
    ¬ Law3588.TermDefinableFromFin Law692 :=
  not_termDefinableFromFin_of_aff R81.aa R81.bb R81.kk
    ((@Law692.models_iff R81 aff692).mpr aff692_sat692)
    fun q r hm ↦
      let h := (@Law3588.models_iff R81 (aff692Fam q r)).mp hm
      aff692_cov3588 q r (h 0 0 0) (h 1 0 0) (h 0 1 0) (h 0 0 1)
