import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status
import Mathlib.Data.Fin.VecNotation

/-!
# Sound symmetry breaking for finite-spectrum searches

Relabeling conjugates the squaring map. A checked list of representatives of
finite endofunctions therefore reduces the squaring maps that a refutation must
consider. These are functional directed graphs (cycles with incoming trees),
not necessarily DAGs. No restriction on the off-diagonal entries is assumed.
-/

open Law Law.MagmaLaw
namespace Spectrum.Symmetry

def conjugate {n : ℕ} (p : Equiv.Perm (Fin n)) (s : Fin n → Fin n) : Fin n → Fin n :=
  fun x => p (s (p.symm x))

/-- A completeness certificate for a collection of squaring-map representatives. -/
def Covers (n : ℕ) (representatives : List (Fin n → Fin n)) : Prop :=
  ∀ s, ∃ p : Equiv.Perm (Fin n), conjugate p s ∈ representatives

/-- Every finite model can be relabeled to have a representative squaring map. -/
theorem canonical_model {n : ℕ} {representatives : List (Fin n → Fin n)}
    (complete : Covers n representatives) (L : NatMagmaLaw) (h : L.HasModel n) :
    ∃ M : Magma (Fin n), @satisfies _ (Fin n) M L ∧
      (fun x => M.op x x) ∈ representatives := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨p, hp⟩ := complete (fun x => M.op x x)
  exact ⟨M.transport p,
    (@satisfies_equiv _ _ _ M (M.transport p) (M.transportEquiv p) L).mp hM, hp⟩

end Spectrum.Symmetry
