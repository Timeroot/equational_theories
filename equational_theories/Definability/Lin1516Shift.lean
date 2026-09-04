import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import equational_theories.Definability.CloneTraps
import equational_theories.Equations.All

/-!
# The shifted affine model of 1516 over `ZMod 19`, and its two traps

`Definability/Lin1516.lean` uses the `GF(16)` model `x ◇ y = 10 x + 6 y`, whose clone is all `256`
linear maps. The affine models of `1516` over a field are `x ◇ y = a x + b y + k` with

    a b (1 + b) = 1,     a² + a b + b³ = 0,     k (a + b² + b + 1) = 0,

and the last condition normally forces `k = 0`. It does not at `19`: there `b = 13` is a root of
`b³ - b + 1`, so `a = 1 - b = 7`, and then `a + b² + b + 1 = 190 = 0`, leaving `k` free. The
resulting `x ◇ y = 7 x + 13 y + 1` is a model of `1516` that the `k = 0` family cannot reach —
`y ◇ y = y + 1`, so it does *not* satisfy `63`, and its automorphism group is the nineteen
translations rather than `AGL(1, 19)`.

Its clone is easy to describe. Every coefficient sum is `7 + 13 = 1`, so a term of `◇` is

    □(x, y) = α x + (1 - α) y + γ,

and there are exactly `361` of those, all reached. Of them `55` fail to generate `◇` back, and
they are precisely the two universal traps of `Definability/CloneTraps.lean`:

* `Magma.DiagFixed` — the `19` maps with `γ = 0`, which are idempotent because `α + (1 - α) = 1`;
* `Magma.IgnoreArg` — the `38` maps with `α = 0` or `α = 1`, which are `y + γ` and `x + γ`.

`◇` itself is in neither — `0 ◇ 0 = 1` and it depends on both arguments — so any target realised
only by trapped maps is not term-structural from `1516`, over finite magmas and hence over all of
them. That is the three targets below; each of them forces `γ = 0`.

Because the operations here have weight one there is no need for a packed multiplication table:
`ZMod 19` is a field on the nose, the clone-closure step is a ring identity in the symbolic
coefficient `1 - 7` and never has to know that `1 - 7 = 13`, and the coverage checks are `361`
coefficient pairs at two assignments each.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace Magma

/-- The affine operation `α x + (1 - α) y + γ` over `ZMod 19`; weight one by construction. -/
@[implicit_reducible]
def faff19 (al ga : ZMod 19) : Magma (ZMod 19) := ⟨fun x y ↦ al * x + (1 - al) * y + ga⟩

/-- The model `x ◇ y = 7 x + 13 y + 1` of equation 1516 over `ZMod 19`. -/
@[implicit_reducible]
def aff1516 : Magma (ZMod 19) := faff19 7 1

/-- Being an affine map of weight one. This is the whole clone of `Magma.aff1516`. -/
def Aff19 (u : ZMod 19 → ZMod 19 → ZMod 19) : Prop := ∃ al ga, (faff19 al ga).op = u

/-- The weight-one affine maps are closed under composition along `Magma.aff1516`, so they contain
its whole clone. Weight one is what makes this a ring identity: the composite of `α₁ x + (1-α₁) y
+ γ₁` and `α₂ x + (1-α₂) y + γ₂` has first coefficient `7α₁ + (1-7)α₂`, and its second coefficient
is `7(1-α₁) + (1-7)(1-α₂) = 1 - (7α₁ + (1-7)α₂)` without ever evaluating `1 - 7`. -/
theorem aff1516_isCloneInvariant : aff1516.IsCloneInvariant Aff19 where
  fst := ⟨1, 0, by funext x y; show (1 : ZMod 19) * x + (1 - 1) * y + 0 = x; ring⟩
  snd := ⟨0, 0, by funext x y; show (0 : ZMod 19) * x + (1 - 0) * y + 0 = y; ring⟩
  comp := by
    rintro _ _ ⟨a1, g1, rfl⟩ ⟨a2, g2, rfl⟩
    refine ⟨7 * a1 + (1 - 7) * a2, 7 * g1 + (1 - 7) * g2 + 1, ?_⟩
    funext x y
    show (7 * a1 + (1 - 7) * a2) * x + (1 - (7 * a1 + (1 - 7) * a2)) * y
        + (7 * g1 + (1 - 7) * g2 + 1)
      = 7 * (a1 * x + (1 - a1) * y + g1) + (1 - 7) * (a2 * x + (1 - a2) * y + g2) + 1
    ring

/-- The two traps, as a family indexed by `Fin 2`. -/
def affQ : Fin 2 → (ZMod 19 → ZMod 19 → ZMod 19) → Prop
  | 0 => DiagFixed
  | 1 => IgnoreArg

/-- Membership in the union of the two traps, in terms of the coefficients: no shift, or
degenerate. On the clone of `Magma.aff1516` this is exactly the set of members that fail to
generate `◇` back. -/
def Aff19Trapped (al ga : ZMod 19) : Prop := ga = 0 ∨ al = 0 ∨ al = 1

instance (al ga : ZMod 19) : Decidable (Aff19Trapped al ga) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Each arithmetic shape lands in the trap it names. A shiftless weight-one map is idempotent
because `α x + (1 - α) x = x`, and `α ∈ {0, 1}` kills one of the two coefficients. -/
theorem affQ_of_trapped (al ga : ZMod 19) (h : Aff19Trapped al ga) :
    ∃ k, affQ k (faff19 al ga).op := by
  rcases h with rfl | rfl | rfl
  · exact ⟨0, fun x ↦ by show al * x + (1 - al) * x + 0 = x; ring⟩
  · exact ⟨1, true, fun x x' y ↦ by
      show (0 : ZMod 19) * x + (1 - 0) * y + ga = 0 * x' + (1 - 0) * y + ga; ring⟩
  · exact ⟨1, false, fun x y y' ↦ by
      show (1 : ZMod 19) * x + (1 - 1) * y + ga = 1 * x + (1 - 1) * y' + ga; ring⟩

/-- Each trap is a clone invariant of any magma satisfying it; both are generic. -/
theorem affQ_isCloneInvariant (k : Fin 2) (N : Magma (ZMod 19)) :
    affQ k N.op → N.IsCloneInvariant (affQ k) := by
  fin_cases k
  · exact fun h ↦ DiagFixed.isCloneInvariant h
  · exact fun h ↦ IgnoreArg.isCloneInvariant h

/-- The diamond is in neither trap: `0 ◇ 0 = 1`, and it depends on both arguments. -/
theorem aff1516_notQ : ∀ k, ¬ affQ k aff1516.op := by
  intro k
  fin_cases k
  · exact (by decide : ¬ DiagFixed aff1516.op)
  · exact (by decide : ¬ IgnoreArg aff1516.op)

end Magma

theorem aff1516_satisfies_1516 : @Equation1516 (ZMod 19) Magma.aff1516 := by decide

/-- `x = x ◇ ((x ◇ x) ◇ x)` forces a weight-one affine map into a trap: it forces `γ = 0`. -/
theorem aff1516_cov99 : ∀ al ga : ZMod 19,
    (0 : ZMod 19) = ((Magma.faff19 al ga).op 0 ((Magma.faff19 al ga).op
      ((Magma.faff19 al ga).op 0 0) 0)) →
    (1 : ZMod 19) = ((Magma.faff19 al ga).op 1 ((Magma.faff19 al ga).op
      ((Magma.faff19 al ga).op 1 1) 1)) →
    Magma.Aff19Trapped al ga := by decide

theorem Equation99_not_termStructuralFromFin_Equation1516 :
    ¬ Law99.TermStructuralFromFin Law1516 :=
  not_termStructuralFromFin_of_invariant Magma.aff1516
    ((@Law1516.models_iff (ZMod 19) Magma.aff1516).mpr aff1516_satisfies_1516)
    Magma.aff1516_isCloneInvariant Magma.affQ_isCloneInvariant Magma.aff1516_notQ
    fun u hu hm ↦ by
      obtain ⟨al, ga, rfl⟩ := hu
      have h := (@Law99.models_iff (ZMod 19) (Magma.faff19 al ga)).mp hm
      exact Magma.affQ_of_trapped al ga (aff1516_cov99 al ga (h 0) (h 1))

/-- `x = x ◇ (((x ◇ x) ◇ x) ◇ x)` forces a weight-one affine map into a trap. -/
theorem aff1516_cov1223 : ∀ al ga : ZMod 19,
    (0 : ZMod 19) = ((Magma.faff19 al ga).op 0 ((Magma.faff19 al ga).op
      ((Magma.faff19 al ga).op ((Magma.faff19 al ga).op 0 0) 0) 0)) →
    (1 : ZMod 19) = ((Magma.faff19 al ga).op 1 ((Magma.faff19 al ga).op
      ((Magma.faff19 al ga).op ((Magma.faff19 al ga).op 1 1) 1) 1)) →
    Magma.Aff19Trapped al ga := by decide

theorem Equation1223_not_termStructuralFromFin_Equation1516 :
    ¬ Law1223.TermStructuralFromFin Law1516 :=
  not_termStructuralFromFin_of_invariant Magma.aff1516
    ((@Law1516.models_iff (ZMod 19) Magma.aff1516).mpr aff1516_satisfies_1516)
    Magma.aff1516_isCloneInvariant Magma.affQ_isCloneInvariant Magma.aff1516_notQ
    fun u hu hm ↦ by
      obtain ⟨al, ga, rfl⟩ := hu
      have h := (@Law1223.models_iff (ZMod 19) (Magma.faff19 al ga)).mp hm
      exact Magma.affQ_of_trapped al ga (aff1516_cov1223 al ga (h 0) (h 1))

/-- `x ◇ x = (x ◇ x) ◇ (x ◇ x)` forces a weight-one affine map into a trap. -/
theorem aff1516_cov3659 : ∀ al ga : ZMod 19,
    ((Magma.faff19 al ga).op 0 0) = ((Magma.faff19 al ga).op ((Magma.faff19 al ga).op 0 0)
      ((Magma.faff19 al ga).op 0 0)) →
    ((Magma.faff19 al ga).op 1 1) = ((Magma.faff19 al ga).op ((Magma.faff19 al ga).op 1 1)
      ((Magma.faff19 al ga).op 1 1)) →
    Magma.Aff19Trapped al ga := by decide

theorem Equation3659_not_termStructuralFromFin_Equation1516 :
    ¬ Law3659.TermStructuralFromFin Law1516 :=
  not_termStructuralFromFin_of_invariant Magma.aff1516
    ((@Law1516.models_iff (ZMod 19) Magma.aff1516).mpr aff1516_satisfies_1516)
    Magma.aff1516_isCloneInvariant Magma.affQ_isCloneInvariant Magma.aff1516_notQ
    fun u hu hm ↦ by
      obtain ⟨al, ga, rfl⟩ := hu
      have h := (@Law3659.models_iff (ZMod 19) (Magma.faff19 al ga)).mp hm
      exact Magma.affQ_of_trapped al ga (aff1516_cov3659 al ga (h 0) (h 1))
