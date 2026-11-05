import equational_theories.Parastrophes.FiniteQuasigroups
import equational_theories.Parastrophes.ImageBasis

/-!
# A two-equation basis for E917's finite left-division image

For the proposed division operation D, put `c(x)=(x*(x*x))*x`.
The exact finite basis consists of E1020, `x=x*c(x)`, and
`x=y*(c(x)*(x*y))`. These have four and six operations respectively.
Multiplication is recovered by the five-operation term `c(y)*(y*x)`.

The key calculation recovers the original square as c. If M is the source
operation and s=M(x,x), then D(x,x)=M(s,s). Choose b with M(b,s)=x.
Take b=M(s,M(M(s,s),x)). E917 and cancellation of the two outer rows
give M(b,s)=x. Two further instances give M(x,b)=M(s,s), so
b=D(x,D(x,x)); consequently D(b,x)=s. This recovery calculation works
on arbitrary carriers whenever left division exists. Finiteness is used
only when the image basis supplies surjectivity and we need injectivity.
There is no finite-table certificate or bounded square-map-period assumption.

The two-equation basis is recorded separately from the still-open question
of whether a single identity characterizes the image.
-/
namespace Parastrophes.Eq917Image
open Law FreeMagma

def core {G : Type} (D : Magma G) (x : G) := D.op (D.op x (D.op x x)) x

def Cross {G : Type} (D : Magma G) : Prop :=
  ∀ x y, x = D.op y (D.op (core D x) (D.op x y))

def Basis {G : Type} (D : Magma G) : Prop := @Equation1020 G D ∧ Cross D

/-- Two diagonal calculations identify a source square in division language. -/
theorem core_eq_square {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation917 G M) (x : G) :
    core D x = M.op x x := by
  let s := M.op x x
  let b := M.op s (M.op (M.op s s) x)
  have hb : M.op b s = x := by
    have he := congrArg (fun z => D.op (M.op s s) (D.op s z)) (h b s)
    simpa only [b, hd.2] using he.symm
  change M.op b (M.op x x) = x at hb
  have hdiag : D.op x x = M.op (M.op x x) (M.op x x) := by
    have he := congrArg (D.op x) (h x x)
    simpa only [hd.2] using he
  have he := h b (M.op x x)
  rw [hb] at he
  have he' := h (M.op (M.op x x) (M.op x x)) x
  rw [← he] at he'
  have hb' : b = D.op x (D.op x x) := by
    have hh := congrArg (D.op x) he'
    rw [hd.2, ← hdiag] at hh
    exact hh.symm
  unfold core
  rw [← hb']
  exact (congrArg (D.op b) hb).symm.trans (hd.2 b (M.op x x))

/-- This is a uniform term, not a power whose exponent depends on the order. -/
theorem multiplication_eq {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation917 G M) (x y : G) :
    M.op x y = D.op (core D y) (D.op y x) := by
  have he := congrArg (fun z => D.op (M.op y y) (D.op y z)) (h x y)
  simpa only [hd.2, core_eq_square M D hd h] using he.symm

theorem forward {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation917 G M) : Basis D := by
  constructor
  · intro x
    change x = D.op x (core D x)
    rw [core_eq_square M D hd h, hd.2]
  · intro x y
    rw [← multiplication_eq M D hd h y x, hd.2]

theorem backward {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : Basis D) : @Equation917 G M := by
  have hc (x : G) : M.op x x = core D x := by
    have he := congrArg (M.op x) (h.1 x)
    simpa only [core, hd.1] using he
  intro x y
  have he := congrArg (fun z => M.op y (M.op (core D y) (M.op x z))) (h.2 y x)
  simpa only [hd.1, hc] using he.symm

theorem characterizes_fin {G : Type} [Finite G] (D : Magma G) :
    Basis D ↔ InImage Law917 .left D := by
  constructor
  · intro h
    let M : Magma G := ⟨fun x y => D.op (core D y) (D.op y x)⟩
    have he (x y : G) : D.op x (M.op x y) = y := (h.2 y x).symm
    have hi (x : G) : Function.Injective (D.op x) :=
      Finite.injective_iff_surjective.mpr (fun y => ⟨_, he x y⟩)
    have hd : IsDivision .left M D :=
      ⟨fun x y => hi x (he x (D.op x y)), he⟩
    exact ⟨M, (@Law917.models_iff G M).mpr (backward M D hd h), hd⟩
  · rintro ⟨M, h, hd⟩
    exact forward M D hd ((@Law917.models_iff G M).mp h)

def crossLaw : NatMagmaLaw :=
  ⟨Lf 0, Lf 1 ⋆ ((((Lf 0 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 1))⟩

private theorem crossLaw_iff {G : Type} (D : Magma G) :
    @satisfies _ G D crossLaw ↔ Cross D := by
  constructor
  · intro h x y; exact h (fun n => if n = 0 then x else y)
  · intro h v; exact h (v 0) (v 1)

/-- Exact finite basis: E1020 and `x=y*(((x*(x*x))*x)*(x*y))`.
The two identities have ten operations in total. -/
@[parastrophe_basis] theorem left917_fin :
    CharacterizesBasis .fin Law917 .left [Law1020, crossLaw] := by
  intro G D hG
  letI : Finite G := hG
  have hb : (∀ t ∈ [Law1020, crossLaw], @satisfies _ G D t) ↔ Basis D := by
    simp [Law1020.models_iff, crossLaw_iff, Basis]
  exact hb.trans (characterizes_fin D)

end Parastrophes.Eq917Image
