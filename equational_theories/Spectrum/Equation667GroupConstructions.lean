import equational_theories.Spectrum.Equation667AutomorphismTwist
import Mathlib.Tactic.Group

/-! What group-based constructions can and cannot do for E667. -/
namespace Spectrum.E667.GroupConstructions

/-- Automorphism-coefficient affine operations over a group satisfy E667
only if the underlying group is abelian. No finiteness is needed. -/
theorem affine_forces_commutative {G : Type*} [Group G] (α β : G ≃* G) (c : G)
    (h : @Equation667 G ⟨fun x y => α x * β y * c⟩) :
    ∀ x y : G, x * y = y * x := by
  let K := β (β (α c))
  let L := β (β c) * β c * c
  have hy (y : G) : α y * K * β (β (β y)) * L = 1 := by
    have hh := (h 1 y).symm
    dsimp only [Magma.op] at hh
    simpa only [map_one, map_mul, one_mul, mul_one, K, L, mul_assoc] using hh
  have h0 : K * L = 1 := by simpa only [map_one, one_mul, mul_one] using hy 1
  have hL : L = K⁻¹ := by
    calc
      L = K⁻¹ * (K * L) := by group
      _ = K⁻¹ := by rw [h0, mul_one]
  have ha (y : G) : α y = K * (β (β (β y)))⁻¹ * K⁻¹ := by
    calc
      α y = (α y * K * β (β (β y)) * L) * (L⁻¹ * (β (β (β y)))⁻¹ * K⁻¹) := by group
      _ = L⁻¹ * (β (β (β y)))⁻¹ * K⁻¹ := by rw [hy, one_mul]
      _ = K * (β (β (β y)))⁻¹ * K⁻¹ := by rw [hL, inv_inv]
  have anti (x y : G) : α (x * y) = α y * α x := by
    rw [ha (x * y), ha y, ha x]
    simp only [map_mul, mul_inv_rev]
    group
  intro x y
  apply α.injective
  calc
    α (x * y) = α y * α x := anti x y
    _ = α (y * x) := (α.map_mul y x).symm

def regularOp {G : Type*} [Group G] (h : G → G) (x y : G) : G := x * h (x⁻¹ * y)

/-- Left multiplication by any group element is an automorphism of a
regular-profile operation. -/
theorem regular_translate {G : Type*} [Group G] (h : G → G) (g x y : G) :
    regularOp h (g * x) (g * y) = g * regularOp h x y := by
  simp only [regularOp, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- The square map in regular coordinates is right multiplication by h(1). -/
theorem regular_square {G : Type*} [Group G] (h : G → G) (x : G) :
    regularOp h x x = x * h 1 := by simp only [regularOp, inv_mul_cancel]

/-- All idempotents or no idempotents: one fixed square determines the
square map on an entire regular orbit. -/
theorem regular_idempotent_iff {G : Type*} [Group G] (h : G → G) (x : G) :
    regularOp h x x = x ↔ h 1 = 1 := by rw [regular_square, mul_eq_left]

/-- An equivariant operation is completely determined by its row at 1. -/
theorem regular_representation {G : Type*} [Group G] (q : G → G → G)
    (hq : ∀ g x y, q (g*x) (g*y) = g*q x y) (x y : G) :
    q x y = regularOp (q 1) x y := by
  have hh := hq x 1 (x⁻¹ * y)
  simpa only [mul_one, mul_inv_cancel_left, regularOp] using hh

/-- Exact profile criterion, over arbitrary groups, for the regular operation
to satisfy E667. It justifies the reduced group-based search encoding. -/
theorem regular_law_iff {G : Type*} [Group G] (h : G → G) :
    @Equation667 G ⟨regularOp h⟩ ↔
      ∀ t, h (t⁻¹ * h (h 1 * h ((h 1)⁻¹ * t))) = t⁻¹ := by
  have at_one (t : G) :
      regularOp h t (regularOp h 1 (regularOp h (regularOp h 1 1) t)) =
        t * h (t⁻¹ * h (h 1 * h ((h 1)⁻¹ * t))) := by
    simp only [regularOp, inv_one, one_mul]
  constructor
  · intro he t
    have hh := (he 1 t).symm
    change regularOp h t (regularOp h 1 (regularOp h (regularOp h 1 1) t)) = 1 at hh
    rw [at_one] at hh
    calc
      h (t⁻¹ * h (h 1 * h ((h 1)⁻¹ * t))) =
          t⁻¹ * (t * h (t⁻¹ * h (h 1 * h ((h 1)⁻¹ * t)))) := by group
      _ = t⁻¹ := by rw [hh, mul_one]
  · intro hp
    have he (t : G) : 1 = regularOp h t (regularOp h 1 (regularOp h (regularOp h 1 1) t)) := by
      rw [at_one, hp, mul_inv_cancel]
    intro x y
    have hh := congrArg (fun z => x * z) (he (x⁻¹ * y))
    simpa only [← regular_translate, mul_one, mul_inv_cancel_left] using hh

/-- Commutativity also has a one-variable profile criterion. -/
theorem regular_commutative_iff {G : Type*} [Group G] (h : G → G) :
    (∀ x y, regularOp h x y = regularOp h y x) ↔ ∀ t, h t = t * h t⁻¹ := by
  constructor
  · intro hc t
    simpa only [regularOp, inv_one, one_mul, mul_one] using hc 1 t
  · intro hp x y
    have hh := congrArg (fun z => x*z) (hp (x⁻¹*y))
    simpa only [regularOp, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using hh

/-- The profile and its complete mapping are bijections exactly when the
regular operation is a quasigroup. This equivalence does not require finiteness. -/
theorem regular_latin_iff {G : Type*} [Group G] (h : G → G) :
    ((∀ x, Function.Bijective (regularOp h x)) ∧
      ∀ y, Function.Bijective (fun x => regularOp h x y)) ↔
      Function.Bijective h ∧ Function.Bijective (fun t => t⁻¹*h t) := by
  constructor
  · rintro ⟨hr,hc⟩
    refine ⟨?_,?_⟩
    · have hh := hr 1
      change Function.Bijective (fun y => (1 : G)*h ((1 : G)⁻¹*y)) at hh
      simpa only [inv_one, one_mul] using hh
    · simpa only [Function.comp_def, regularOp, inv_inv, mul_one] using
        (hc 1).comp inv_involutive.bijective
  · rintro ⟨hh,hd⟩
    constructor
    · intro x
      simpa only [Function.comp_def, regularOp] using
        (Equiv.mulLeft x).bijective.comp (hh.comp (Equiv.mulLeft x⁻¹).bijective)
    · intro y
      have he (x : G) : regularOp h x y = y*((x⁻¹*y)⁻¹*h (x⁻¹*y)) := by
        simp only [regularOp, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
      simpa only [Function.comp_def, he] using
        (Equiv.mulLeft y).bijective.comp (hd.comp ((Equiv.mulRight y).bijective.comp inv_involutive.bijective))

/-- In finite regular E667 models, both the profile and its associated
complete mapping are permutations. -/
theorem regular_permutations {G : Type*} [Group G] [Finite G] (h : G → G)
    (he : @Equation667 G ⟨regularOp h⟩) :
    Function.Bijective h ∧ Function.Bijective (fun t => t⁻¹ * h t) := by
  letI : Magma G := ⟨regularOp h⟩
  have hi : Function.Injective h := by
    intro x y hh
    apply E667883.left_injective667 he 1
    simpa only [Magma.op, regularOp, inv_one, one_mul] using hh
  have hd : Function.Injective (fun t => t⁻¹ * h t) := by
    intro x y hh
    have heq : x⁻¹ = y⁻¹ := by
      apply E667883.right_injective667 he 1
      simpa only [Magma.op, regularOp, inv_inv, mul_one] using hh
    exact inv_injective heq
  exact ⟨⟨hi, Finite.injective_iff_surjective.mp hi⟩,
    ⟨hd, Finite.injective_iff_surjective.mp hd⟩⟩

spectrum_assert regular_latin_iff complete
spectrum_assert regular_law_iff complete
spectrum_assert regular_permutations complete

spectrum_assert affine_forces_commutative complete
spectrum_assert regular_representation complete
end Spectrum.E667.GroupConstructions
