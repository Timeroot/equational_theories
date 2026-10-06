import equational_theories.Spectrum.Equation667GroupConstructions
import equational_theories.Spectrum.Equation667BinaryDesignExistence
import equational_theories.Spectrum.Equation667BinaryDesignCount

/-! A nonmedial five-point design algebra of order 21 from the nonabelian
group C7 ⋊ C3. Its E667 proof checks only the 21 profile equations. -/
namespace Spectrum.E667.Frobenius21

@[ext] structure Carrier where
  a : ZMod 7
  b : ZMod 3
  deriving DecidableEq, Fintype

instance : Mul Carrier := ⟨fun x y => ⟨x.a + 2^x.b.val*y.a, x.b+y.b⟩⟩
instance : One Carrier := ⟨⟨0,0⟩⟩
instance : Inv Carrier := ⟨fun x => ⟨-(2^(3-x.b.val)*x.a), -x.b⟩⟩

private theorem power_add (b d : ZMod 3) :
    (2 : ZMod 7)^(b+d).val = 2^b.val * 2^d.val := by
  fin_cases b <;> fin_cases d <;> decide +kernel

private theorem power_neg (b : ZMod 3) :
    (2 : ZMod 7)^(-b).val = 2^(3-b.val) := by
  fin_cases b <;> decide +kernel

instance : Group Carrier where
  mul_assoc x y z := by
    obtain ⟨a,b⟩ := x
    obtain ⟨c,d⟩ := y
    obtain ⟨e,f⟩ := z
    apply Carrier.ext
    · change a+2^b.val*c+2^(b+d).val*e = a+2^b.val*(c+2^d.val*e)
      rw [power_add]
      ring
    · change b+d+f=b+(d+f)
      ring
  one_mul x := by
    apply Carrier.ext <;> change _ = _
    · change 0+2^(0 : ZMod 3).val*x.a=x.a
      norm_num
    · exact zero_add _
  mul_one x := by
    apply Carrier.ext
    · change x.a+2^x.b.val*0=x.a
      simp
    · exact add_zero _
  inv_mul_cancel x := by
    obtain ⟨a,b⟩ := x
    apply Carrier.ext
    · change -(2^(3-b.val)*a)+2^(-b).val*a = 0
      rw [power_neg]
      ring
    · exact neg_add_cancel _

def decode (n : ℕ) : Carrier := ⟨n,(n/7 : ℕ)⟩
def profile (x : Carrier) : Carrier := decode
  (![![0,3,12,20,17,10,2], ![16,11,14,4,9,19,1], ![8,7,18,5,15,6,13]] x.b x.a)

theorem profile_identity : profile 1 = 1 := by decide +kernel

/-- Only one original-law instance per translation orbit needs checking. -/
theorem law : @Equation667 Carrier ⟨GroupConstructions.regularOp profile⟩ := by
  apply (GroupConstructions.regular_law_iff profile).mpr
  rintro ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem idempotent (x : Carrier) : GroupConstructions.regularOp profile x x = x :=
  (GroupConstructions.regular_idempotent_iff profile x).mpr profile_identity

theorem commutative (x y : Carrier) :
    GroupConstructions.regularOp profile x y = GroupConstructions.regularOp profile y x := by
  apply (GroupConstructions.regular_commutative_iff profile).mpr
  rintro ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem nonmedial : ¬ ∀ x y z w : Carrier,
    GroupConstructions.regularOp profile (GroupConstructions.regularOp profile x y)
      (GroupConstructions.regularOp profile z w) =
    GroupConstructions.regularOp profile (GroupConstructions.regularOp profile x z)
      (GroupConstructions.regularOp profile y w) := by
  intro hh
  have hn : GroupConstructions.regularOp profile (GroupConstructions.regularOp profile (decode 0) (decode 0))
      (GroupConstructions.regularOp profile (decode 1) (decode 4)) ≠
    GroupConstructions.regularOp profile (GroupConstructions.regularOp profile (decode 0) (decode 1))
      (GroupConstructions.regularOp profile (decode 0) (decode 4)) := by decide +kernel
  exact hn (hh _ _ _ _)

theorem card : Nat.card Carrier = 21 := by
  let e : Carrier ≃ ZMod 7 × ZMod 3 := {
    toFun := fun x => (x.a,x.b)
    invFun := fun x => ⟨x.1,x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp

/-- A noncommutative, nonmedial double cover of the explicit nonabelian
21-point design, with exactly 21 idempotents and the original design as quotient. -/
theorem nonlinear_double_cover :
    ∃ op : (Carrier × ZMod 2) → (Carrier × ZMod 2) → (Carrier × ZMod 2),
      @Equation667 (Carrier × ZMod 2) ⟨op⟩ ∧
      (∀ x, op x x = (x.1,0)) ∧
      (∀ x y, (op x y).1 = GroupConstructions.regularOp profile x.1 y.1) ∧
      (¬ ∀ x y, op x y = op y x) ∧
      (¬ ∀ x y z w, op (op x y) (op z w) = op (op x z) (op y w)) ∧
      Nat.card {x : Carrier × ZMod 2 // op x x = x} = 21 := by
  letI : Magma Carrier := ⟨GroupConstructions.regularOp profile⟩
  letI : Nontrivial Carrier := ⟨⟨decode 0,decode 1,by decide +kernel⟩⟩
  simpa only [card] using BinaryDesignExistence.exists_deformation law commutative idempotent

theorem double_card : Nat.card (Carrier × ZMod 2) = 42 := by
  rw [Nat.card_prod, card, Nat.card_zmod]

/-- This single 21-point quotient has exactly 2^105 labelled binary cocycles,
or 2^84 after putting each fiber's unique idempotent at zero. -/
theorem binary_extension_counts :
    Nat.card {C : Carrier → Carrier → ZMod 2 //
      BinaryExtensions.Cocycle (GroupConstructions.regularOp profile) C} = 2^105 ∧
    Nat.card {C : Carrier → Carrier → ZMod 2 // (∀ x, C x x = 0) ∧
      BinaryExtensions.Cocycle (GroupConstructions.regularOp profile) C} = 2^84 := by
  classical
  letI : Magma Carrier := ⟨GroupConstructions.regularOp profile⟩
  let B := @BinaryDesignExistence.blockSet Carrier _
  let e := BinaryDesignExistence.coordinates law commutative idempotent
  have cover := BinaryDesignExistence.cover law commutative idempotent
  have hbase : BinaryDesign.base B e = GroupConstructions.regularOp profile := by
    funext x y
    exact BinaryDesignExistence.base_eq law commutative idempotent x y
  have hb : Nat.card (CommutativeDesign.Block Carrier) = 21 := by
    have hh := CommutativeDesign.pair_count law commutative idempotent
    rw [card] at hh
    omega
  have hall := BinaryDesign.all_count B e cover
  have hnorm := BinaryDesign.normalized_count B e cover
  change Nat.card {C : Carrier → Carrier → ZMod 2 //
    BinaryExtensions.Cocycle (BinaryDesign.base B e) C} = _ at hall
  change Nat.card {C : Carrier → Carrier → ZMod 2 // (∀ x, C x x = 0) ∧
    BinaryExtensions.Cocycle (BinaryDesign.base B e) C} = _ at hnorm
  rw [hbase, card, hb] at hall
  rw [hbase, hb] at hnorm
  exact ⟨hall,hnorm⟩

spectrum_assert binary_extension_counts complete
spectrum_assert nonlinear_double_cover complete
spectrum_assert double_card complete
spectrum_assert commutative complete
spectrum_assert nonmedial complete
spectrum_assert law complete
end Spectrum.E667.Frobenius21
