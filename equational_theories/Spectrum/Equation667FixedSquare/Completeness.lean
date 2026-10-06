import equational_theories.Spectrum.Equation667FixedSquare.Cases
import equational_theories.Spectrum.Equation667FixedSquare.Normalization

namespace Spectrum.E667.FixedSquare
open RightIdentityTwelve (Holds)
open Spectrum.FiniteSearch

def normalizeCase (i : Fin 77) : Bool := decide (i.val ∈ [7,15,30,56])

/-- Refutations of the 77 representatives exclude every bijective square map,
including tables whose original labels have none of our normal forms. -/
theorem no_injective_of_refuted
    (hs : ∀ i, (natNormalized (Cases.table i) (normalizeCase i)).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f)
    (hi : Function.Injective (fun x => f x x)) : False := by
  let d : Equiv.Perm (Fin 12) := Equiv.ofBijective (fun x => f x x)
    ⟨hi, Finite.injective_iff_surjective.mp hi⟩
  obtain ⟨i,hc⟩ := Cases.exists_conjugate d
  obtain ⟨e,he⟩ := isConj_iff.mp hc
  let g := relabel f e
  have hg : Holds g := RightIdentityTwelve.holds_relabel h e
  have hgd (x : Fin 12) : g x x = Cases.table i x := by
    have hh := congrArg (fun p : Equiv.Perm (Fin 12) => p x) he
    exact hh
  exact no_model_normalized (Cases.table i) (normalizeCase i) (hs i) g hg hgd

spectrum_assert no_injective_of_refuted complete
end Spectrum.E667.FixedSquare
