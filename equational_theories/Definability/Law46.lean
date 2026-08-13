import Batteries.Data.List.Basic
import equational_theories.Definability.Basic
import equational_theories.Definability.Simple
import equational_theories.Equations.All

/-!
# Definability of the constant law 46

Equation 46, `x ◇ y = z ◇ w`, says that the magma operation is constant. This file collects the
ways it can be term-defined from other laws.

The first is a syntactic criterion: if the two sides of `L` have the same shape but disjoint
variables, then `L` forces every term of that shape to be constant.

The second, `Equation46_termDefinableFrom_of_constantTerm`, only asks that `L` force some *unary*
term `t` to take the same value on every element; then `x □ y := t(x)` is a constant operation
given by a term in `◇`. It is applied below to the eleven laws
`3350`, `4295`, `4297`, `4303`, `4325`, `4411`, `4423`, `4461`, `4485`, `4497` and `4535`,
which are exactly the laws found by a finite-model search to plausibly force a small unary term
to be constant, minus equation 898. (Equation 898, `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`, is satisfied
by `x ◇ y = b³ x + b y` on the field with eight elements, where `b` has multiplicative order 7;
in that magma every unary term evaluates to `x` itself, so no unary term is constant there.)

Since equation 46 implies equation 40, `x ◇ x = y ◇ y`, each of these also gives term-definability
of law 40, via `Law40_termDefinableFrom_Law46` and `TermDefinable.trans`.
-/

open FirstOrder.Language
open Law
open Law.MagmaLaw

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from any law `lhs = rhs`, where
lhs and rhs are the same shape, but with disjoint sets of variables. -/
theorem Equation46_termDefinableFrom_equalShape {L : NatMagmaLaw}
  (hShape : L.lhs ⬝ (fun _ ↦ Lf 0) = L.rhs ⬝ (fun _ ↦ Lf 0) := by rfl)
  (hDisjoint : L.lhs.elems.val.Disjoint L.rhs.elems := by rw [List.Disjoint]; decide +kernel)
  : Law46.TermDefinableFrom L := by
  --There are two cases: there is at least one function application, or both sides of L are leaves.
  cases hlhs : L.lhs
  next x =>
    --In this case, the law is of the form x = y. Thus, it is (equivalent to) equation 2
    obtain ⟨y,hy⟩ : ∃ y, L.rhs = Lf y := sorry
    have hxy : x ≠ y := sorry
    rw [show L = Lf x ≃ Lf y from sorry]
    clear hlhs hy hShape hDisjoint
    apply termDefinable_of_termStructural
    apply termStructural_of_implies
    have : (Lf x ≃ Lf y).toFin.toNat = Law2 := by
      -- have h₁ : (Lf x ≃ Lf y : NatMagmaLaw).elems.1 = [x,y] := by
      --   sorry
      -- have h₂ : Fin ((Lf x ≃ Lf y : NatMagmaLaw).elems).1.length = Fin 2 := by
      --   rw [h₁]
      --   simp
      -- simp [toFin, h₁]
      -- simp_rw [h₁]
      sorry
    unfold implies
    simp_rw [← satisfies_toFin (E := Lf x ≃ Lf y)
            , ← satisfies_toNat (E := (Lf x ≃ Lf y).toFin),
            this]
    exact Equation2_implies Law46
  --Otherwise we call back to the more interesting case of a function application
  intro G M hGL
  use ⟨fun x _ ↦ @Term.realize _ _ M.FOStructure _ (fun _ ↦ x) L.lhs.toTerm⟩
  constructor
  · rw [@Law46.models_iff]
    by_cases hG : Nonempty G
    · suffices ∃ c, ∀ (x y : G), x ◇ y = c by
        obtain ⟨c,h⟩ := this
        intros x y z w
        simp
        sorry
      sorry
    · exact (not_nonempty_iff.mp hG).elim
  · use (MagmaLanguage.lhomWithConstants _).onTerm (L.lhs.toTerm.subst fun a ↦ var 0)
    funext v
    sorry

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from Equation 40 `x ◇ x = y ◇ y`. -/
theorem Equation46_termDefinableFrom_Equation40 : Law46.TermDefinableFrom Law40 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4276 `x ◇ (x ◇ x) = y ◇ (y ◇ y)`. -/
theorem Equation46_termDefinableFrom_Equation4276 : Law46.TermDefinableFrom Law4276 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4308 `x ◇ (x ◇ y) = z ◇ (z ◇ w)`. -/
theorem Equation46_termDefinableFrom_Equation4308 : Law46.TermDefinableFrom Law4308 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4336 `x ◇ (y ◇ x) = z ◇ (w ◇ z)`. -/
theorem Equation46_termDefinableFrom_Equation4336 : Law46.TermDefinableFrom Law4336 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4355 `x ◇ (y ◇ y) = z ◇ (w ◇ w)`. -/
theorem Equation46_termDefinableFrom_Equation4355 : Law46.TermDefinableFrom Law4355 :=
  Equation46_termDefinableFrom_equalShape

/-- If a law `L` forces the unary term `t` to be constant, then the constant law 46
`x ◇ y = z ◇ w` is term-definable from `L`: the operation `x □ y := t(x)` works. -/
theorem Equation46_termDefinableFrom_of_constantTerm {L : NatMagmaLaw} (t : FreeMagma ℕ)
    (ht : ∀ {G : Type} [Magma G], satisfies G L → ∀ x y : G,
      t ⬝ (fun _ ↦ x) = t ⬝ (fun _ ↦ y)) :
    Law46.TermDefinableFrom L := by
  intro G M hGL
  refine ⟨⟨fun x _ ↦ t ⬝ (fun _ ↦ x)⟩, ?_, ?_⟩
  · rw [@Law46.models_iff]
    exact fun x _ z _ ↦ ht hGL x z
  · letI := M.FOStructure
    rw [Set.termDefinable_empty_iff]
    refine ⟨t.toTerm.subst fun _ ↦ Term.var 0, ?_⟩
    funext v
    simp [Magma.FinArityOp]

/-- Law 46 `x ◇ y = z ◇ w` implies law 40 `x ◇ x = y ◇ y`. -/
theorem Law46_implies_Law40 : Law46.implies Law40 := fun {_G} _ h ↦
  Law40.models_iff.mpr fun x y ↦ (Law46.models_iff.mp h) x x y y

/-- Law 40 `x ◇ x = y ◇ y` is term-definable from law 46 `x ◇ y = z ◇ w`; combine this with
`TermDefinable.trans` to get law 40 from any of the laws below. -/
theorem Law40_termDefinableFrom_Law46 : Law40.TermDefinableFrom Law46 :=
  termDefinable_of_termStructural (termStructural_of_implies Law46_implies_Law40)

/-- Law 3350 `x ◇ y = y ◇ (x ◇ (z ◇ z))` forces the term `(x ◇ x) ◇ (x ◇ x)` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation3350 :
    Law46.TermDefinableFrom Law3350 :=
  Equation46_termDefinableFrom_of_constantTerm ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) fun hG x y ↦ by
    have h := Law3350.models_iff.mp hG
    show (x ◇ x) ◇ (x ◇ x) = (y ◇ y) ◇ (y ◇ y)
    calc (x ◇ x) ◇ (x ◇ x)
      _ = (x ◇ x) ◇ ((x ◇ x) ◇ (y ◇ y)) := h (x ◇ x) (x ◇ x) y
      _ = ((x ◇ x) ◇ (y ◇ y)) ◇ ((x ◇ x) ◇ (y ◇ y)) := h (x ◇ x) ((x ◇ x) ◇ (y ◇ y)) y
      _ = ((x ◇ x) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x))) :=
          congrArg (((x ◇ x) ◇ (y ◇ y)) ◇ ·) (h (x ◇ x) (y ◇ y) x)
      _ = (y ◇ y) ◇ ((x ◇ x) ◇ (y ◇ y)) := (h (y ◇ y) ((x ◇ x) ◇ (y ◇ y)) (x ◇ x)).symm
      _ = (y ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x))) := congrArg ((y ◇ y) ◇ ·) (h (x ◇ x) (y ◇ y) x)
      _ = (y ◇ y) ◇ (y ◇ y) := (h (y ◇ y) (y ◇ y) (x ◇ x)).symm

/-- Law 4295 `x ◇ (x ◇ y) = y ◇ (z ◇ x)` forces the term `(x ◇ x) ◇ (x ◇ (x ◇ x))` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4295 :
    Law46.TermDefinableFrom Law4295 :=
  Equation46_termDefinableFrom_of_constantTerm
    ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) fun hG x y ↦ by
    have h := Law4295.models_iff.mp hG
    show (x ◇ x) ◇ (x ◇ (x ◇ x)) = (y ◇ y) ◇ (y ◇ (y ◇ y))
    calc (x ◇ x) ◇ (x ◇ (x ◇ x))
      _ = (x ◇ x) ◇ (x ◇ (y ◇ x)) := congrArg ((x ◇ x) ◇ ·) (h x x y)
      _ = (y ◇ x) ◇ ((y ◇ x) ◇ (x ◇ x)) := (h (y ◇ x) (x ◇ x) x).symm
      _ = (x ◇ x) ◇ (y ◇ (y ◇ x)) := h (y ◇ x) (x ◇ x) y
      _ = (x ◇ x) ◇ (x ◇ (y ◇ y)) := congrArg ((x ◇ x) ◇ ·) (h y x y)
      _ = (y ◇ y) ◇ ((y ◇ y) ◇ (x ◇ x)) := (h (y ◇ y) (x ◇ x) x).symm
      _ = (x ◇ x) ◇ ((x ◇ x) ◇ (y ◇ y)) := h (y ◇ y) (x ◇ x) (x ◇ x)
      _ = (y ◇ y) ◇ (y ◇ (x ◇ x)) := h (x ◇ x) (y ◇ y) y
      _ = (y ◇ y) ◇ (x ◇ (x ◇ y)) := congrArg ((y ◇ y) ◇ ·) ((h x y x).symm)
      _ = (x ◇ y) ◇ ((x ◇ y) ◇ (y ◇ y)) := (h (x ◇ y) (y ◇ y) x).symm
      _ = (y ◇ y) ◇ (y ◇ (x ◇ y)) := h (x ◇ y) (y ◇ y) y
      _ = (y ◇ y) ◇ (y ◇ (y ◇ y)) := congrArg ((y ◇ y) ◇ ·) ((h y y x).symm)

/-- Law 4297 `x ◇ (x ◇ y) = y ◇ (z ◇ z)` forces the term `x ◇ (x ◇ (x ◇ x))` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4297 :
    Law46.TermDefinableFrom Law4297 :=
  Equation46_termDefinableFrom_of_constantTerm (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) fun hG x y ↦ by
    have h := Law4297.models_iff.mp hG
    show x ◇ (x ◇ (x ◇ x)) = y ◇ (y ◇ (y ◇ y))
    calc x ◇ (x ◇ (x ◇ x))
      _ = (x ◇ x) ◇ (x ◇ x) := h x (x ◇ x) x
      _ = y ◇ (y ◇ (x ◇ x)) := (h y (x ◇ x) x).symm
      _ = y ◇ (y ◇ (y ◇ y)) := congrArg (y ◇ ·) ((h y y x).symm)

/-- Law 4303 `x ◇ (x ◇ y) = z ◇ (y ◇ x)` forces the term `x ◇ (x ◇ (x ◇ x))` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4303 :
    Law46.TermDefinableFrom Law4303 :=
  Equation46_termDefinableFrom_of_constantTerm (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) fun hG x y ↦ by
    have h := Law4303.models_iff.mp hG
    show x ◇ (x ◇ (x ◇ x)) = y ◇ (y ◇ (y ◇ y))
    calc x ◇ (x ◇ (x ◇ x))
      _ = (x ◇ x) ◇ ((x ◇ x) ◇ x) := h x (x ◇ x) (x ◇ x)
      _ = (y ◇ y) ◇ (x ◇ (x ◇ x)) := h (x ◇ x) x (y ◇ y)
      _ = (y ◇ y) ◇ ((y ◇ y) ◇ (x ◇ x)) := congrArg ((y ◇ y) ◇ ·) (h x x (y ◇ y))
      _ = y ◇ ((x ◇ x) ◇ (y ◇ y)) := h (y ◇ y) (x ◇ x) y
      _ = y ◇ (y ◇ (y ◇ y)) := congrArg (y ◇ ·) ((h y y (x ◇ x)).symm)

/-- Law 4325 `x ◇ (y ◇ x) = y ◇ (z ◇ z)` forces the term `x ◇ ((x ◇ x) ◇ x)` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4325 :
    Law46.TermDefinableFrom Law4325 :=
  Equation46_termDefinableFrom_of_constantTerm (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) fun hG x y ↦ by
    have h := Law4325.models_iff.mp hG
    show x ◇ ((x ◇ x) ◇ x) = y ◇ ((y ◇ y) ◇ y)
    calc x ◇ ((x ◇ x) ◇ x)
      _ = (x ◇ x) ◇ (x ◇ x) := h x (x ◇ x) x
      _ = (y ◇ y) ◇ ((x ◇ x) ◇ (y ◇ y)) := (h (y ◇ y) (x ◇ x) x).symm
      _ = (y ◇ y) ◇ (x ◇ ((x ◇ x) ◇ x)) := congrArg ((y ◇ y) ◇ ·) ((h x (x ◇ x) y).symm)
      _ = (y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x)) := congrArg ((y ◇ y) ◇ ·) (h x (x ◇ x) x)
      _ = y ◇ ((y ◇ y) ◇ y) := (h y (y ◇ y) (x ◇ x)).symm

/-- Law 4411 `x ◇ (x ◇ y) = (y ◇ z) ◇ x` forces the term `(x ◇ x) ◇ (x ◇ x)` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4411 :
    Law46.TermDefinableFrom Law4411 :=
  Equation46_termDefinableFrom_of_constantTerm ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) fun hG x y ↦ by
    have h := Law4411.models_iff.mp hG
    show (x ◇ x) ◇ (x ◇ x) = (y ◇ y) ◇ (y ◇ y)
    calc (x ◇ x) ◇ (x ◇ x)
      _ = (x ◇ x) ◇ ((x ◇ x) ◇ x) := (h (x ◇ x) x x).symm
      _ = ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) := (h ((x ◇ x) ◇ x) x x).symm
      _ = (x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ x) := h ((x ◇ x) ◇ x) x (x ◇ x)
      _ = ((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := congrArg (· ◇ ((x ◇ x) ◇ x)) (h x x x)
      _ = ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (x ◇ x)) := (h ((x ◇ x) ◇ x) (x ◇ x) x).symm
      _ = ((x ◇ x) ◇ y) ◇ ((x ◇ x) ◇ x) := h ((x ◇ x) ◇ x) (x ◇ x) y
      _ = (y ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ x) := congrArg (· ◇ ((x ◇ x) ◇ x)) ((h y x x).symm)
      _ = ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ y) := (h ((x ◇ x) ◇ x) y (y ◇ x)).symm
      _ = ((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ (x ◇ x))) := congrArg (((x ◇ x) ◇ x) ◇ ·) ((h y (x ◇ x) x).symm)
      _ = ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ y) ◇ y) := congrArg (((x ◇ x) ◇ x) ◇ ·) (h y (x ◇ x) y)
      _ = ((x ◇ x) ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y) :=
          congrArg (((x ◇ x) ◇ x) ◇ ·) (congrArg (· ◇ y) ((h y x x).symm))
      _ = ((x ◇ x) ◇ x) ◇ (y ◇ (y ◇ y)) := congrArg (((x ◇ x) ◇ x) ◇ ·) ((h y y (y ◇ x)).symm)
      _ = ((x ◇ x) ◇ x) ◇ ((y ◇ y) ◇ y) := congrArg (((x ◇ x) ◇ x) ◇ ·) (h y y y)
      _ = ((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (x ◇ x)) := (h ((y ◇ y) ◇ y) (x ◇ x) x).symm
      _ = ((x ◇ x) ◇ y) ◇ ((y ◇ y) ◇ y) := h ((y ◇ y) ◇ y) (x ◇ x) y
      _ = (y ◇ (y ◇ x)) ◇ ((y ◇ y) ◇ y) := congrArg (· ◇ ((y ◇ y) ◇ y)) ((h y x x).symm)
      _ = ((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y) := (h ((y ◇ y) ◇ y) y (y ◇ x)).symm
      _ = (y ◇ y) ◇ ((y ◇ y) ◇ y) := h ((y ◇ y) ◇ y) y y
      _ = (y ◇ y) ◇ (y ◇ y) := h (y ◇ y) y y

/-- Law 4423 `x ◇ (x ◇ y) = (z ◇ z) ◇ x` forces the term `(x ◇ x) ◇ (x ◇ x)` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4423 :
    Law46.TermDefinableFrom Law4423 :=
  Equation46_termDefinableFrom_of_constantTerm ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) fun hG x y ↦ by
    have h := Law4423.models_iff.mp hG
    show (x ◇ x) ◇ (x ◇ x) = (y ◇ y) ◇ (y ◇ y)
    calc (x ◇ x) ◇ (x ◇ x)
      _ = (x ◇ x) ◇ ((x ◇ x) ◇ x) := (h (x ◇ x) x x).symm
      _ = ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) := (h ((x ◇ x) ◇ x) x x).symm
      _ = (y ◇ y) ◇ ((x ◇ x) ◇ x) := h ((x ◇ x) ◇ x) x y
      _ = (y ◇ y) ◇ (x ◇ (x ◇ x)) := congrArg ((y ◇ y) ◇ ·) ((h x x x).symm)
      _ = (y ◇ y) ◇ ((y ◇ y) ◇ x) := congrArg ((y ◇ y) ◇ ·) (h x x y)
      _ = (y ◇ y) ◇ (y ◇ y) := h (y ◇ y) x y

/-- Law 4461 `x ◇ (y ◇ x) = (z ◇ z) ◇ y` forces the term `x ◇ (x ◇ (x ◇ x))` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4461 :
    Law46.TermDefinableFrom Law4461 :=
  Equation46_termDefinableFrom_of_constantTerm (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) fun hG x y ↦ by
    have h := Law4461.models_iff.mp hG
    show x ◇ (x ◇ (x ◇ x)) = y ◇ (y ◇ (y ◇ y))
    calc x ◇ (x ◇ (x ◇ x))
      _ = x ◇ ((x ◇ x) ◇ x) := congrArg (x ◇ ·) (h x x x)
      _ = (x ◇ x) ◇ (x ◇ x) := h x (x ◇ x) x
      _ = y ◇ ((x ◇ x) ◇ y) := (h y (x ◇ x) x).symm
      _ = y ◇ (y ◇ (y ◇ y)) := congrArg (y ◇ ·) ((h y y x).symm)

/-- Law 4485 `x ◇ (y ◇ y) = (y ◇ z) ◇ x` forces the term `(x ◇ x) ◇ (x ◇ x)` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4485 :
    Law46.TermDefinableFrom Law4485 :=
  Equation46_termDefinableFrom_of_constantTerm ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) fun hG x y ↦ by
    have h := Law4485.models_iff.mp hG
    show (x ◇ x) ◇ (x ◇ x) = (y ◇ y) ◇ (y ◇ y)
    calc (x ◇ x) ◇ (x ◇ x)
      _ = (x ◇ (x ◇ x)) ◇ (x ◇ x) := h (x ◇ x) x (x ◇ x)
      _ = (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)) := h (x ◇ (x ◇ x)) x (x ◇ x)
      _ = ((x ◇ x) ◇ x) ◇ (x ◇ (x ◇ x)) := congrArg (· ◇ (x ◇ (x ◇ x))) (h x x x)
      _ = ((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := congrArg (((x ◇ x) ◇ x) ◇ ·) (h x x x)
      _ = ((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)) := (h ((x ◇ x) ◇ x) (x ◇ x) x).symm
      _ = ((x ◇ x) ◇ y) ◇ ((x ◇ x) ◇ x) := h ((x ◇ x) ◇ x) (x ◇ x) y
      _ = (y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ x) := congrArg (· ◇ ((x ◇ x) ◇ x)) ((h y x x).symm)
      _ = ((x ◇ x) ◇ x) ◇ (y ◇ y) := (h ((x ◇ x) ◇ x) y (x ◇ x)).symm
      _ = (y ◇ y) ◇ ((x ◇ x) ◇ (x ◇ x)) := (h (y ◇ y) (x ◇ x) x).symm
      _ = ((x ◇ x) ◇ y) ◇ (y ◇ y) := h (y ◇ y) (x ◇ x) y
      _ = (y ◇ (x ◇ x)) ◇ (y ◇ y) := congrArg (· ◇ (y ◇ y)) ((h y x x).symm)
      _ = (y ◇ y) ◇ (y ◇ y) := (h (y ◇ y) y (x ◇ x)).symm

/-- Law 4497 `x ◇ (y ◇ y) = (z ◇ z) ◇ x` forces the term `(x ◇ x) ◇ (x ◇ x)` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4497 :
    Law46.TermDefinableFrom Law4497 :=
  Equation46_termDefinableFrom_of_constantTerm ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) fun hG x y ↦ by
    have h := Law4497.models_iff.mp hG
    show (x ◇ x) ◇ (x ◇ x) = (y ◇ y) ◇ (y ◇ y)
    calc (x ◇ x) ◇ (x ◇ x)
      _ = (y ◇ y) ◇ (x ◇ x) := h (x ◇ x) x y
      _ = (y ◇ y) ◇ (y ◇ y) := h (y ◇ y) x y

/-- Law 4535 `x ◇ (y ◇ z) = (y ◇ w) ◇ x` forces the term `(x ◇ x) ◇ (x ◇ x)` to be constant,
so the constant law 46 is term-definable from it. -/
theorem Equation46_termDefinableFrom_Equation4535 :
    Law46.TermDefinableFrom Law4535 :=
  Equation46_termDefinableFrom_of_constantTerm ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) fun hG x y ↦ by
    have h := Law4535.models_iff.mp hG
    show (x ◇ x) ◇ (x ◇ x) = (y ◇ y) ◇ (y ◇ y)
    calc (x ◇ x) ◇ (x ◇ x)
      _ = (x ◇ (x ◇ x)) ◇ (x ◇ x) := h (x ◇ x) x x (x ◇ x)
      _ = (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)) := h (x ◇ (x ◇ x)) x x (x ◇ x)
      _ = ((x ◇ x) ◇ x) ◇ (x ◇ (x ◇ x)) := congrArg (· ◇ (x ◇ (x ◇ x))) (h x x x x)
      _ = ((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := congrArg (((x ◇ x) ◇ x) ◇ ·) (h x x x x)
      _ = ((x ◇ x) ◇ y) ◇ ((x ◇ x) ◇ x) := h ((x ◇ x) ◇ x) (x ◇ x) x y
      _ = ((x ◇ x) ◇ y) ◇ ((x ◇ x) ◇ y) := h ((x ◇ x) ◇ y) (x ◇ x) x y
      _ = (y ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ y) := congrArg (· ◇ ((x ◇ x) ◇ y)) ((h y x x x).symm)
      _ = ((x ◇ x) ◇ y) ◇ (y ◇ y) := (h ((x ◇ x) ◇ y) y y (x ◇ x)).symm
      _ = (y ◇ (x ◇ x)) ◇ (y ◇ y) := congrArg (· ◇ (y ◇ y)) ((h y x x x).symm)
      _ = (y ◇ y) ◇ (y ◇ y) := (h (y ◇ y) y y (x ◇ x)).symm
