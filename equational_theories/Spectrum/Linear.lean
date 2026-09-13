import equational_theories.Spectrum.Basic
import equational_theories.EquationLawConversion
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
A checked coefficient test for linear models. An identity between integer linear
forms holds in every abelian group, in particular in `ZMod n` for every positive `n`.
The same evaluation lemma can also certify individual modular models.
-/

open Law FreeMagma
open scoped BigOperators

namespace Spectrum

/-- Integer linear operations on an arbitrary abelian group. -/
@[implicit_reducible]
def linear {G : Type*} [AddCommGroup G] (a b : ℤ) : Magma G :=
  ⟨fun x y => a • x + b • y⟩

/-- The coefficient of each variable after expanding a term. -/
def coefficients {k : ℕ} (a b : ℤ) : FreeMagma (Fin k) → Fin k → ℤ
  | .Leaf i => fun j => if j = i then 1 else 0
  | .Fork s t => fun j => a * coefficients a b s j + b * coefficients a b t j

theorem eval_linear {G : Type*} [AddCommGroup G] {k : ℕ} (a b : ℤ)
    (φ : Fin k → G) (t : FreeMagma (Fin k)) :
    @evalInMagma _ _ (linear a b) φ t = ∑ i, coefficients a b t i • φ i := by
  induction t with
  | Leaf i => simp [evalInMagma, coefficients]
  | Fork s t hs ht =>
    change a • @evalInMagma _ _ (linear a b) φ s +
      b • @evalInMagma _ _ (linear a b) φ t = _
    simp only [hs, ht, coefficients, add_smul, mul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]

/-- Restrict bounded variable indices without the noncomputable casts in `L.toFin`. -/
def restrict (L : NatMagmaLaw) (k : ℕ) (h : L.bounded k) : MagmaLaw (Fin k) :=
  L.pmap fun i hi => ⟨i, MagmaLaw.bounded_iff.mp h i hi⟩

theorem satisfies_of_restrict {G : Type*} [Magma G] (L : NatMagmaLaw)
    (k : ℕ) (hb : L.bounded k) (h : satisfies G (restrict L k hb)) : satisfies G L := by
  intro φ
  exact (satisfiesPhi_pmap (φ := fun i : Fin k => φ i.val) (ψ := φ) L
    (fun i hi => ⟨i, MagmaLaw.bounded_iff.mp hb i hi⟩) (fun _ _ => rfl)).mp
    (h (fun i => φ i.val))

/-- Equality of coefficient vectors is a finite, kernel-checkable certificate.
Six variables suffice for all of the original 4694 equations. -/
def LinearCertificate (L : NatMagmaLaw) (a b : ℤ) : Prop :=
  if h : L.bounded 6 then
    coefficients a b (restrict L 6 h).lhs = coefficients a b (restrict L 6 h).rhs
  else False

instance (L : NatMagmaLaw) (a b : ℤ) : Decidable (LinearCertificate L a b) := by
  unfold LinearCertificate
  split <;> infer_instance

theorem satisfies_of_linearCertificate {G : Type*} [AddCommGroup G]
    (L : NatMagmaLaw) (a b : ℤ) (h : LinearCertificate L a b) :
    @satisfies _ G (linear a b) L := by
  letI := linear (G := G) a b
  unfold LinearCertificate at h
  split at h
  next hb =>
    apply satisfies_of_restrict L 6 hb
    intro φ
    change @evalInMagma _ _ (linear a b) φ (restrict L 6 hb).lhs =
      @evalInMagma _ _ (linear a b) φ (restrict L 6 hb).rhs
    rw [eval_linear, eval_linear, h]
  next => exact h.elim

theorem full_of_linear (L : NatMagmaLaw) (a b : ℤ) (h : LinearCertificate L a b) :
    L.HasFullSpectrum := by
  intro n
  by_cases hn : n = 0
  · subst n; exact L.hasModel_zero
  · letI : NeZero n := ⟨hn⟩
    exact Law.MagmaLaw.hasModel_of_card (linear (G := ZMod n) a b)
      (satisfies_of_linearCertificate L a b h) (ZMod.card n)

end Spectrum
