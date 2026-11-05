import equational_theories.Parastrophes.AffineIdentityCertificate
import equational_theories.Parastrophes.Equation872ImageBasis
import Mathlib.Algebra.DualNumber
import Mathlib.Data.ZMod.Basic

/-! Three 25-element affine countermodels over the dual numbers F5[ε], ε²=0.
Research indices below are indices in the saved rewrite campaign, not law IDs.
Each certificate checks only four affine coefficients in the 25-element ring. -/
namespace Parastrophes.Eq872NilpotentCandidates
open Law FreeMagma AffineIdentityCertificate
open scoped DualNumber
abbrev R := DualNumber (ZMod 5)
instance : Finite R := inferInstanceAs (Finite (ZMod 5 × ZMod 5))
instance : DecidableEq R := inferInstanceAs (DecidableEq (ZMod 5 × ZMod 5))

@[implicit_reducible] def commutative : Magma R := affine (3+ε) (3+ε) 0

def commutativeTerms : List (FreeMagma (Fin 3)) := [
  -- 10611
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0))),
  -- 10880
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0))),
  -- 24228
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ ((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0))),
  -- 24241
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ ((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24448
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ ((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0))),
  -- 24462
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ ((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))]

theorem commutative_coefficients : ∀ t ∈ commutativeTerms,
    coefficients (R := R) (3+ε) (3+ε) 0 t = ⟨1,0,0,0⟩ := by decide

theorem commutative_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ commutativeTerms) :
    @satisfies _ R commutative (identity t) :=
  satisfies_of_coefficients (3+ε) (3+ε) 0 t (commutative_coefficients t ht)

theorem commutative_not_image : ¬ InImage Law872 .left commutative := by
  rintro ⟨M, hM, hd⟩
  have h := (Eq872Image.forward M commutative hd ((@Law872.models_iff _ M).mp hM)).2 (0 : R) (1 : R)
  exact (by decide : (0 : R) ≠ commutative.op 1 (commutative.op (Eq872Image.core commutative 0) (commutative.op 1 0))) h

theorem commutative_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ commutativeTerms) :
    ¬ Characterizes .fin Law872 .left (identity t) := by
  intro h
  exact commutative_not_image ((h R commutative (inferInstance : Finite R)).mp (commutative_satisfies t ht))

@[implicit_reducible] def idempotent : Magma R := affine (-1+ε) (2-ε) 0

def idempotentTerms : List (FreeMagma (Fin 3)) := [
  -- 10650
  ((Lf 1 ⋆ (((Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10919
  ((Lf 2 ⋆ (((Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 24268
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ ((((Lf 0 ⋆ Lf 1) ⋆ (((Lf 0 ⋆ Lf 1) ⋆ (Lf 0 ⋆ Lf 1)) ⋆ (Lf 0 ⋆ Lf 1))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24490
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ ((((Lf 0 ⋆ Lf 2) ⋆ (((Lf 0 ⋆ Lf 2) ⋆ (Lf 0 ⋆ Lf 2)) ⋆ (Lf 0 ⋆ Lf 2))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 2))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 25778
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 0 ⋆ ((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 29588
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 0 ⋆ ((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem idempotent_coefficients : ∀ t ∈ idempotentTerms,
    coefficients (R := R) (-1+ε) (2-ε) 0 t = ⟨1,0,0,0⟩ := by decide

theorem idempotent_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ idempotentTerms) :
    @satisfies _ R idempotent (identity t) :=
  satisfies_of_coefficients (-1+ε) (2-ε) 0 t (idempotent_coefficients t ht)

theorem idempotent_not_image : ¬ InImage Law872 .left idempotent := by
  rintro ⟨M, hM, hd⟩
  have h := (Eq872Image.forward M idempotent hd ((@Law872.models_iff _ M).mp hM)).2 (0 : R) (1 : R)
  exact (by decide : (0 : R) ≠ idempotent.op 1 (idempotent.op (Eq872Image.core idempotent 0) (idempotent.op 1 0))) h

theorem idempotent_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ idempotentTerms) :
    ¬ Characterizes .fin Law872 .left (identity t) := by
  intro h
  exact idempotent_not_image ((h R idempotent (inferInstance : Finite R)).mp (idempotent_satisfies t ht))

@[implicit_reducible] def shifted : Magma R := affine (3+ε) 3 1

def shiftedTerms : List (FreeMagma (Fin 3)) := [
  -- 14360
  (Lf 1 ⋆ ((Lf 0 ⋆ ((((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 15020
  (Lf 2 ⋆ ((Lf 0 ⋆ ((((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 16110
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 17598
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 18505
  ((((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 18823
  ((((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 35460
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 35735
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 35740
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 36389
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 36660
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 36663
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 37651
  ((((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 37695
  ((((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 38455
  (Lf 1 ⋆ ((Lf 0 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ ((((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))) ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 38635
  (Lf 1 ⋆ ((Lf 0 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 40259
  (Lf 2 ⋆ ((Lf 0 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ ((((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))) ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 40438
  (Lf 2 ⋆ ((Lf 0 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))]

theorem shifted_coefficients : ∀ t ∈ shiftedTerms,
    coefficients (R := R) (3+ε) 3 1 t = ⟨1,0,0,0⟩ := by decide

theorem shifted_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ shiftedTerms) :
    @satisfies _ R shifted (identity t) :=
  satisfies_of_coefficients (3+ε) 3 1 t (shifted_coefficients t ht)

theorem shifted_not_image : ¬ InImage Law872 .left shifted := by
  rintro ⟨M, hM, hd⟩
  have h := (Eq872Image.forward M shifted hd ((@Law872.models_iff _ M).mp hM)).2 (0 : R) (1 : R)
  exact (by decide : (0 : R) ≠ shifted.op 1 (shifted.op (Eq872Image.core shifted 0) (shifted.op 1 0))) h

theorem shifted_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ shiftedTerms) :
    ¬ Characterizes .fin Law872 .left (identity t) := by
  intro h
  exact shifted_not_image ((h R shifted (inferInstance : Finite R)).mp (shifted_satisfies t ht))

theorem commutative_comm (x y : R) : commutative.op x y = commutative.op y x := by
  change (3+ε)*x+(3+ε)*y+0 = (3+ε)*y+(3+ε)*x+0
  ring

theorem idempotent_idem (x : R) : idempotent.op x x = x := by
  change (-1+ε)*x+(2-ε)*x+0 = x
  ring

private theorem unit_three_eps : IsUnit (3+ε : R) :=
  isUnit_iff_exists_inv.mpr ⟨2+ε, by decide⟩

theorem commutative_quasigroup : IsQuasigroup commutative :=
  quasigroup_fin _ _ _ unit_three_eps unit_three_eps

theorem idempotent_quasigroup : IsQuasigroup idempotent :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨-1-ε, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨3-ε, by decide⟩)

theorem shifted_quasigroup : IsQuasigroup shifted :=
  quasigroup_fin _ _ _ unit_three_eps (isUnit_iff_exists_inv.mpr ⟨2, by decide⟩)

end Parastrophes.Eq872NilpotentCandidates
