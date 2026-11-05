import equational_theories.Parastrophes.FiniteCrossedIdentity
import equational_theories.Parastrophes.ImageBasis
import equational_theories.Equations.All

/-!
# E481's finite left-division image

In division notation, the image has a right identity e and satisfies
`x * (y * x) = e * y`. The identity element is itself the parameter-free
term `c(x) = x * (x * (x * x))`. Thus two pure magma identities suffice:

* E440: `x = x * c(y)`;
* E4332: `x * (y * x) = z * (y * z)`.

The converse must establish bijectivity rather than assume it. That is exactly
the finite stable-image argument in `FiniteCrossedIdentity.quasigroup`.
Forward translation works on arbitrary carriers whenever left division exists.
The finite exact basis does not yet settle whether one identity suffices.
-/
namespace Parastrophes.Eq481Image
open Law FreeMagma

def core {G : Type*} (D : Magma G) (x : G) := D.op x (D.op x (D.op x x))

def Basis {G : Type*} (D : Magma G) : Prop :=
  (∀ x y, x = D.op x (core D y)) ∧
  (∀ x y z, D.op x (D.op y x) = D.op z (D.op y z))

/-- E481 has constant squares once left division exists. -/
theorem square_constant {G : Type*} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation481 G M) (x y : G) :
    M.op x x = M.op y y := by
  have he := (h x x x).symm.trans (h x x y)
  have hh := congrArg (fun z => D.op x (D.op x (D.op x z))) he
  simpa only [hd.2] using hh

/-- The translated crossed law and right identity are available without
finiteness; the existence of division is the required hypothesis here. -/
theorem translated {G : Type*} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation481 G M) (a : G) :
    (∀ x, D.op x (M.op a a) = x) ∧
    (∀ x y, D.op x (D.op y x) = D.op (M.op a a) y) := by
  let e := M.op a a
  have hs (x : G) : M.op x x = e := square_constant M D hd h x a
  have unit (x : G) : D.op x e = x := by rw [← hs x, hd.2]
  have formula (x y : G) : D.op x y = M.op y (M.op x e) := by
    have he := congrArg (D.op x) (h y x a)
    simpa only [hd.2] using he
  refine ⟨unit, ?_⟩
  intro x y
  rw [formula y x, hd.2, formula e y, hs e]

theorem forward {G : Type*} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation481 G M) : Basis D := by
  have hc (x : G) : core D x = M.op x x := by
    obtain ⟨unit, cross⟩ := translated M D hd h x
    unfold core
    rw [cross x x, cross x (M.op x x), unit]
  constructor
  · intro x y
    rw [hc y]
    exact ((translated M D hd h y).1 x).symm
  · intro x y z
    obtain ⟨_, cross⟩ := translated M D hd h x
    rw [cross x y, cross z y]

/-- The right-unital crossed presentation translates back to E481. -/
theorem backward {G : Type*} (M D : Magma G) (hd : IsDivision .left M D)
    (e : G) (unit : ∀ x, D.op x e = x)
    (cross : ∀ x y, D.op x (D.op y x) = D.op e y) : @Equation481 G M := by
  have hs (x : G) : M.op x x = e := by
    have hh := hd.1 x e
    rwa [unit] at hh
  have he (y : G) : D.op e y = M.op y e := by
    have hh := congrArg (M.op y) (cross y e)
    simpa only [hd.1, unit] using hh
  intro x y z
  rw [hs z]
  have hh := congrArg (fun t => M.op y (M.op x t)) (cross x y)
  simpa only [hd.1, he] using hh

/-- Recovering multiplication reduces to inverting the unary map `e*x`.
This does not assert that its inverse is a uniform magma term. -/
theorem multiplication_of_inverse {G : Type*} (M D : Magma G)
    (hd : IsDivision .left M D) (e : G)
    (cross : ∀ x y, D.op x (D.op y x) = D.op e y)
    (i : G → G) (hi : ∀ y, D.op e (i y) = y) (x y : G) :
    M.op x y = D.op (i y) x := by
  have hh := congrArg (M.op x) (cross x (i y))
  simpa only [hd.1, hi] using hh.symm

theorem characterizes_fin {G : Type} [Finite G] (D : Magma G) :
    Basis D ↔ InImage Law481 .left D := by
  constructor
  · intro h
    classical
    cases isEmpty_or_nonempty G with
    | inl he =>
      letI := he
      exact ⟨D, fun v => isEmptyElim (v 0), ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩⟩
    | inr he =>
      letI := he
      let e := core D (Classical.arbitrary G)
      have unit (x : G) : D.op x e = x := (h.1 x _).symm
      have cross (x y : G) : D.op x (D.op y x) = D.op e y := by
        simpa only [unit] using h.2 x y e
      have hq := FiniteCrossedIdentity.quasigroup D e unit cross
      let M : Magma G := ⟨fun x y => (Equiv.ofBijective (D.op x) (hq.1 x)).symm y⟩
      have hd : IsDivision .left M D :=
        ⟨fun x y => (Equiv.ofBijective (D.op x) (hq.1 x)).symm_apply_apply y,
          fun x y => (Equiv.ofBijective (D.op x) (hq.1 x)).apply_symm_apply y⟩
      exact ⟨M, (@Law481.models_iff G M).mpr (backward M D hd e unit cross), hd⟩
  · rintro ⟨M, h, hd⟩
    exact forward M D hd ((@Law481.models_iff G M).mp h)

def unitLaw : NatMagmaLaw :=
  ⟨Lf 0, Lf 0 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 1)))⟩

def crossLaw : NatMagmaLaw :=
  ⟨Lf 0 ⋆ (Lf 1 ⋆ Lf 0), Lf 2 ⋆ (Lf 1 ⋆ Lf 2)⟩

private theorem unitLaw_iff {G : Type} (D : Magma G) :
    @satisfies _ G D unitLaw ↔ ∀ x y, x = D.op x (core D y) := by
  constructor
  · intro h x y; exact h (fun n => if n = 0 then x else y)
  · intro h v; exact h (v 0) (v 1)

private theorem crossLaw_iff {G : Type} (D : Magma G) :
    @satisfies _ G D crossLaw ↔
      ∀ x y z, D.op x (D.op y x) = D.op z (D.op y z) := by
  constructor
  · intro h x y z; exact h (fun n => if n = 0 then x else if n = 1 then y else z)
  · intro h v; exact h (v 0) (v 1) (v 2)

/-- Eight operations in total, with no assumed cancellation or finite tables. -/
@[parastrophe_basis] theorem left481_fin :
    CharacterizesBasis .fin Law481 .left [Law440, Law4332] := by
  intro G D hG
  letI : Finite G := hG
  have hb : (∀ t ∈ [unitLaw, crossLaw], @satisfies _ G D t) ↔ Basis D := by
    simp [unitLaw_iff, crossLaw_iff, Basis]
  exact hb.trans (characterizes_fin D)

end Parastrophes.Eq481Image
