import equational_theories.Spectrum.Equation667AffineStructure
import Mathlib.Data.ZMod.Basic

/-! Universal affine E667 constructions on the square and cube of any abelian
group. These are integral companion matrices, so no field is required. -/
namespace Spectrum.E667.AffineStructure
variable (A : Type*) [AddCommGroup A]

def productEnd {U V : Type*} [AddCommGroup U] [AddCommGroup V]
    (f : AddMonoid.End U) (g : AddMonoid.End V) : AddMonoid.End (U × V) where
  toFun x := (f x.1,g x.2)
  map_zero' := by simp
  map_add' x y := by simp

/-- Direct products preserve the affine form as well as E667. -/
theorem product_law {U V : Type*} [AddCommGroup U] [AddCommGroup V]
    (f g : AddMonoid.End U) (c : U) (f' g' : AddMonoid.End V) (c' : V)
    (h : @Equation667 U ⟨op f g c⟩) (h' : @Equation667 V ⟨op f' g' c'⟩) :
    @Equation667 (U × V) ⟨op (productEnd f f') (productEnd g g') (c,c')⟩ := by
  intro x y
  exact Prod.ext (h x.1 y.1) (h' x.2 y.2)

def squareMatrix : AddMonoid.End (A × A) where
  toFun x := (-x.2,x.1)
  map_zero' := by simp
  map_add' x y := by simp [add_comm]

def cubeMatrix : AddMonoid.End (A × A × A) where
  toFun x := (x.2.2,x.1+x.2.2,x.2.1)
  map_zero' := by simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change (x.1+y.1)+(x.2.2+y.2.2) = (x.1+x.2.2)+(y.1+y.2.2)
        abel
      · rfl

theorem squareMatrix_relation : (squareMatrix A)^2+1 = 0 := by
  apply AddMonoidHom.ext
  rintro ⟨a,b⟩
  change (-a,-b)+(a,b) = (0,0)
  simp

theorem cubeMatrix_relation : (cubeMatrix A)^3-cubeMatrix A-1 = 0 := by
  apply AddMonoidHom.ext
  rintro ⟨a,b,c⟩
  change (a+c,b+(a+c),c+b)-(c,a+c,b)-(a,b,c) = (0,0,0)
  apply Prod.ext
  · change a+c-c-a=0
    abel
  · apply Prod.ext
    · change b+(a+c)-(a+c)-b=0
      abel
    · change c+b-b-c=0
      abel

theorem squareMatrix_law :
    @Equation667 (A × A) ⟨normalizedOp (squareMatrix A) 0⟩ := by
  apply (law_iff _ _).mpr
  constructor
  · rw [factor_P, squareMatrix_relation, zero_mul, zero_mul]
  · exact map_zero _

theorem cubeMatrix_law :
    @Equation667 (A × A × A) ⟨normalizedOp (cubeMatrix A) 0⟩ := by
  apply (law_iff _ _).mpr
  constructor
  · rw [factor_P, cubeMatrix_relation, mul_zero, zero_mul]
  · exact map_zero _

theorem square_carrier_card (n : ℕ) [NeZero n] :
    Nat.card (ZMod n × ZMod n) = n^2 := by simp [pow_two]

theorem cube_carrier_card (n : ℕ) [NeZero n] :
    Nat.card (ZMod n × ZMod n × ZMod n) = n^3 := by
  simp [pow_succ, mul_assoc]

omit A in
/-- The coefficient polynomial itself supplies the inverse of B, even on
an infinite abelian group. No finite-injective-surjective argument is used. -/
theorem coefficient_bijective {U : Type*} [AddCommGroup U]
    (g : AddMonoid.End U) (hp : P g = 0) : Function.Bijective g := by
  let t : AddMonoid.End U := g^7-g^5-g^3
  have hgt : g*t = 1 := by
    calc g*t = P g+1 := by dsimp [t,P]; noncomm_ring
         _ = 1 := by rw [hp,zero_add]
  have htg : t*g = 1 := by
    calc t*g = P g+1 := by dsimp [t,P]; noncomm_ring
         _ = 1 := by rw [hp,zero_add]
  have hleft (x : U) : t (g x) = x := by
    simpa only [end_mul_apply, end_one_apply] using congrArg (fun f : AddMonoid.End U => f x) htg
  have hright (x : U) : g (t x) = x := by
    simpa only [end_mul_apply, end_one_apply] using congrArg (fun f : AddMonoid.End U => f x) hgt
  exact ⟨Function.LeftInverse.injective hleft, fun x => ⟨t x,hright x⟩⟩

omit A in
/-- Both affine coefficients are automatically automorphisms, with no
finiteness or initial bijectivity assumption. -/
theorem affine_coefficients_bijective {U : Type*} [AddCommGroup U]
    (f g : AddMonoid.End U) (c : U) (h : @Equation667 U ⟨op f g c⟩) :
    Function.Bijective f ∧ Function.Bijective g := by
  obtain ⟨hf,hp,_⟩ := (full_law_iff f g c).mp h
  have hg := coefficient_bijective g hp
  refine ⟨?_,hg⟩
  rw [hf]
  simpa only [Function.comp_def, pow_succ, pow_zero, end_mul_apply,
    end_one_apply, end_neg_apply] using neg_involutive.bijective.comp (hg.comp (hg.comp hg))

omit A in
/-- Every affine E667 algebra is a quasigroup, including infinite examples. -/
theorem affine_latin {U : Type*} [AddCommGroup U]
    (f g : AddMonoid.End U) (c : U) (h : @Equation667 U ⟨op f g c⟩) :
    (∀ x, Function.Bijective (op f g c x)) ∧
      ∀ y, Function.Bijective (fun x => op f g c x y) := by
  obtain ⟨hf,hg⟩ := affine_coefficients_bijective f g c h
  constructor
  · intro x
    simpa only [Function.comp_def, op] using
      (Equiv.addRight c).bijective.comp ((Equiv.addLeft (f x)).bijective.comp hg)
  · intro y
    simpa only [Function.comp_def, op, add_assoc] using
      (Equiv.addRight (g y+c)).bijective.comp hf

spectrum_assert squareMatrix_law complete
spectrum_assert cubeMatrix_law complete
spectrum_assert product_law complete
spectrum_assert affine_coefficients_bijective complete
spectrum_assert affine_latin complete
end Spectrum.E667.AffineStructure
