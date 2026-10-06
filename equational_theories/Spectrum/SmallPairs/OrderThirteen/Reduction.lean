import equational_theories.Spectrum.SmallPairs.OrderThirteen.Canonical
import equational_theories.Spectrum.SmallPairs.OrderThirteen.Permutations

/-!
After the first row has been fixed, rotations of its other cycles and exchanges
of equally long cycles still give isomorphic tables. Use this freedom twice:
first minimize `f 1 1`, then minimize `f 1 0` while fixing the first choice.
The finite check below supplies actual permutations, not assumptions about
which multiplication tables exist.
-/
namespace Spectrum.SmallPairs.OrderThirteen

/-- The first two-cell and three-cell lists encode the two stages of normalization.
The saved masks are checked together with actual permutations below. -/
def allowed (i : Fin 272) (locked : List (Fin 13)) (z : Fin 13) : Bool :=
  match locked with
  | [_,_] => firstAllowed i z
  | [_,_,t] => secondAllowed i t z
  | _ => true

private def reductionOK (i : Fin 272) (z t : Fin 13) : Bool :=
  let e := reduction i z t
  e 0 == 0 && e 1 == 1 &&
    (List.finRange 13).all (fun x => e (compactRow i x) == compactRow i (e x)) &&
    allowed i [0,1] (e z) && allowed i [0,1,e z] (e t)

@[spectrum_native]
private theorem compactRow_checked : ∀ (i : Fin 272) (x : Fin 13), compactRow i x = row i x := by
  native_decide

@[irreducible] private def allReductionsOK : Bool :=
    (List.finRange 272).all (fun i => (List.finRange 13).all (fun z =>
      (List.finRange 13).all (reductionOK i z)))

@[spectrum_native]
private theorem reductions_checked : allReductionsOK = true := by native_decide

theorem reduction_checked (i : Fin 272) (z t : Fin 13) :
    let e := reduction i z t
    e 0 = 0 ∧ e 1 = 1 ∧ (∀ x, e (row i x) = row i (e x)) ∧
      allowed i [0,1] (e z) = true ∧ allowed i [0,1,e z] (e t) = true := by
  have hall := reductions_checked
  unfold allReductionsOK at hall
  have hi := List.all_eq_true.mp hall i (List.mem_finRange i)
  have hz := List.all_eq_true.mp hi z (List.mem_finRange z)
  have ht := List.all_eq_true.mp hz t (List.mem_finRange t)
  simp only [reductionOK, Bool.and_eq_true] at ht
  obtain ⟨⟨⟨⟨h0,h1⟩,hc⟩,hz⟩,ht⟩ := ht
  refine ⟨beq_iff_eq.mp h0, beq_iff_eq.mp h1, ?_, hz, ht⟩
  intro x
  simpa only [compactRow_checked] using
    beq_iff_eq.mp (List.all_eq_true.mp hc x (List.mem_finRange x))

spectrum_assert reduction_checked complete
end Spectrum.SmallPairs.OrderThirteen
