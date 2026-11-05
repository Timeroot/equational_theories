import equational_theories.Equations.All
import Mathlib.Algebra.Group.Basic

/-! These six laws cannot have a left-bijectivity counterexample of the form
`a x * b y` over any cancellative multiplication, even with arbitrary functions a,b.
In particular this includes all group-based affine constructions. The hypotheses on the representation
are essential: this module does not settle the arbitrary-magma questions. -/
namespace Parastrophes.Separable
variable {G : Type*} [Mul G] [IsCancelMul G]

abbrev magma (a b : G → G) : Magma G where
  op x y := a x * b y

/-- Any E464 operation of the form `a x * b y` has injective rows. -/
theorem left_injective464 (a b : G → G)
    (h : @Equation464 G (magma a b)) (u : G) :
    Function.Injective (fun x => a u * b x) := by
  intro x y hxy
  have hb : b x = b y := mul_left_cancel hxy
  have ha : a x = a y := by
    have hx := (h x x).symm.trans (h x y)
    change (a x * b (a x * b (a x * b (a x * b x)))) = (a y * b (a x * b (a x * b (a x * b y)))) at hx
    simp only [hb] at hx
    exact mul_right_cancel hx
  have hx := h x x
  have hy := h y y
  change x = (a x * b (a x * b (a x * b (a x * b x)))) at hx
  change y = (a y * b (a y * b (a y * b (a y * b y)))) at hy
  simp only [ha, hb] at hx
  exact hx.trans hy.symm

/-- Surjectivity comes directly from E464; cancellation above gives bijectivity. -/
theorem left_bijective464 (a b : G → G)
    (h : @Equation464 G (magma a b)) (u : G) :
    Function.Bijective (fun x => a u * b x) := by
  refine ⟨left_injective464 a b h u, ?_⟩
  intro x
  exact ⟨(a x * b (a x * b (a x * b u))), (h x u).symm⟩

/-- Any E669 operation of the form `a x * b y` has injective rows. -/
theorem left_injective669 (a b : G → G)
    (h : @Equation669 G (magma a b)) (u : G) :
    Function.Injective (fun x => a u * b x) := by
  intro x y hxy
  have hb : b x = b y := mul_left_cancel hxy
  have ha : a x = a y := by
    have hx := (h x x).symm.trans (h x y)
    change (a x * b (a x * b (a (a x * b x) * b x))) = (a y * b (a x * b (a (a x * b y) * b x))) at hx
    simp only [hb] at hx
    exact mul_right_cancel hx
  have hx := h x x
  have hy := h y y
  change x = (a x * b (a x * b (a (a x * b x) * b x))) at hx
  change y = (a y * b (a y * b (a (a y * b y) * b y))) at hy
  simp only [ha, hb] at hx
  exact hx.trans hy.symm

/-- Surjectivity comes directly from E669; cancellation above gives bijectivity. -/
theorem left_bijective669 (a b : G → G)
    (h : @Equation669 G (magma a b)) (u : G) :
    Function.Bijective (fun x => a u * b x) := by
  refine ⟨left_injective669 a b h u, ?_⟩
  intro x
  exact ⟨(a x * b (a (a x * b u) * b x)), (h x u).symm⟩

/-- Any E879 operation of the form `a x * b y` has injective rows. -/
theorem left_injective879 (a b : G → G)
    (h : @Equation879 G (magma a b)) (u : G) :
    Function.Injective (fun x => a u * b x) := by
  intro x y hxy
  have hb : b x = b y := mul_left_cancel hxy
  have ha : a x = a y := by
    have hx := (h x x).symm.trans (h x y)
    change (a x * b (a (a x * b x) * b (a x * b x))) = (a y * b (a (a x * b y) * b (a x * b x))) at hx
    simp only [hb] at hx
    exact mul_right_cancel hx
  have hx := h x x
  have hy := h y y
  change x = (a x * b (a (a x * b x) * b (a x * b x))) at hx
  change y = (a y * b (a (a y * b y) * b (a y * b y))) at hy
  simp only [ha, hb] at hx
  exact hx.trans hy.symm

/-- Surjectivity comes directly from E879; cancellation above gives bijectivity. -/
theorem left_bijective879 (a b : G → G)
    (h : @Equation879 G (magma a b)) (u : G) :
    Function.Bijective (fun x => a u * b x) := by
  refine ⟨left_injective879 a b h u, ?_⟩
  intro x
  exact ⟨(a (a x * b u) * b (a x * b x)), (h x u).symm⟩

/-- Any E1075 operation of the form `a x * b y` has injective rows. -/
theorem left_injective1075 (a b : G → G)
    (h : @Equation1075 G (magma a b)) (u : G) :
    Function.Injective (fun x => a u * b x) := by
  intro x y hxy
  have hb : b x = b y := mul_left_cancel hxy
  have ha : a x = a y := by
    have hx := (h x x).symm.trans (h x y)
    change (a x * b (a (a x * b (a x * b x)) * b x)) = (a y * b (a (a x * b (a x * b y)) * b x)) at hx
    simp only [hb] at hx
    exact mul_right_cancel hx
  have hx := h x x
  have hy := h y y
  change x = (a x * b (a (a x * b (a x * b x)) * b x)) at hx
  change y = (a y * b (a (a y * b (a y * b y)) * b y)) at hy
  simp only [ha, hb] at hx
  exact hx.trans hy.symm

/-- Surjectivity comes directly from E1075; cancellation above gives bijectivity. -/
theorem left_bijective1075 (a b : G → G)
    (h : @Equation1075 G (magma a b)) (u : G) :
    Function.Bijective (fun x => a u * b x) := by
  refine ⟨left_injective1075 a b h u, ?_⟩
  intro x
  exact ⟨(a (a x * b (a x * b u)) * b x), (h x u).symm⟩

/-- Any E1278 operation of the form `a x * b y` has injective rows. -/
theorem left_injective1278 (a b : G → G)
    (h : @Equation1278 G (magma a b)) (u : G) :
    Function.Injective (fun x => a u * b x) := by
  intro x y hxy
  have hb : b x = b y := mul_left_cancel hxy
  have ha : a x = a y := by
    have hx := (h x x).symm.trans (h x y)
    change (a x * b (a (a (a x * b x) * b x) * b x)) = (a y * b (a (a (a x * b x) * b y) * b x)) at hx
    simp only [hb] at hx
    exact mul_right_cancel hx
  have hx := h x x
  have hy := h y y
  change x = (a x * b (a (a (a x * b x) * b x) * b x)) at hx
  change y = (a y * b (a (a (a y * b y) * b y) * b y)) at hy
  simp only [ha, hb] at hx
  exact hx.trans hy.symm

/-- Surjectivity comes directly from E1278; cancellation above gives bijectivity. -/
theorem left_bijective1278 (a b : G → G)
    (h : @Equation1278 G (magma a b)) (u : G) :
    Function.Bijective (fun x => a u * b x) := by
  refine ⟨left_injective1278 a b h u, ?_⟩
  intro x
  exact ⟨(a (a (a x * b x) * b u) * b x), (h x u).symm⟩

/-- Any E1285 operation of the form `a x * b y` has injective rows. -/
theorem left_injective1285 (a b : G → G)
    (h : @Equation1285 G (magma a b)) (u : G) :
    Function.Injective (fun x => a u * b x) := by
  intro x y hxy
  have hb : b x = b y := mul_left_cancel hxy
  have ha : a x = a y := by
    have hx := (h x x).symm.trans (h x y)
    change (a x * b (a (a (a x * b x) * b x) * b x)) = (a y * b (a (a (a x * b y) * b x) * b x)) at hx
    simp only [hb] at hx
    exact mul_right_cancel hx
  have hx := h x x
  have hy := h y y
  change x = (a x * b (a (a (a x * b x) * b x) * b x)) at hx
  change y = (a y * b (a (a (a y * b y) * b y) * b y)) at hy
  simp only [ha, hb] at hx
  exact hx.trans hy.symm

/-- Surjectivity comes directly from E1285; cancellation above gives bijectivity. -/
theorem left_bijective1285 (a b : G → G)
    (h : @Equation1285 G (magma a b)) (u : G) :
    Function.Bijective (fun x => a u * b x) := by
  refine ⟨left_injective1285 a b h u, ?_⟩
  intro x
  exact ⟨(a (a (a x * b u) * b x) * b x), (h x u).symm⟩

end Parastrophes.Separable
