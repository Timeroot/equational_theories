import equational_theories.Spectrum.SmallPairs.OrderThirteen.Rows

set_option maxRecDepth 4096

namespace Spectrum.SmallPairs.OrderThirteen

def cycles (f : Fin 13 → Fin 13) : ℕ → List (Fin 13) → List (List (Fin 13))
  | 0, _ => []
  | _+1, [] => []
  | fuel+1, a::rest =>
    let orbit := a :: ((List.range 12).map (fun j => (f^[j+1]) a)).takeWhile (fun b => b != a)
    orbit :: cycles f fuel (rest.filter (fun b => !(orbit.contains b)))

def order (f : Fin 13 → Fin 13) : List (Fin 13) :=
  match cycles f 13 (List.finRange 13) with
  | [] => []
  | a::rest => a ++ ((rest.mergeSort (fun a b => a.length ≤ b.length)).flatten)

def relabel (f : Fin 13 → Fin 13) : Equiv.Perm (Fin 13) :=
  let table := ((List.finRange 13).map f).toArray
  let cached : Fin 13 → Fin 13 := fun x => table[x.val]!
  ((List.finRange 13).zip (order cached)).foldl
    (fun r ab => r.trans (Equiv.swap ab.1 (r ab.2))) (Equiv.refl _)

def correct (f : Fin 13 → Fin 13) : Bool :=
  let r := relabel f
  let table := (List.finRange 13).map (fun x => r (f (r.symm x)))
  decide (r 0 = 0) && (rows.map (fun g => (List.finRange 13).map g)).contains table

/-- This checks 4096 chain rows, whose exhaustive coverage is a general theorem.
It does not enumerate all permutations of thirteen elements. -/
@[spectrum_native]
theorem canonical_checked : (ChainRows.rows 13 13).all correct = true := by
  native_decide

theorem covers (f : Fin 13 → Fin 13) (hi : Function.Injective f)
    (hc : ∀ i, (f i).val ≤ i.val + 1) :
    relabel f 0 = 0 ∧ ∃ g ∈ rows, ∀ x, relabel f (f x) = g (relabel f x) := by
  have h := List.all_eq_true.mp canonical_checked f (ChainRows.mem_rows f hi hc)
  simp only [correct, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨hzero, ht⟩ := h
  obtain ⟨g, hg, he⟩ := List.mem_map.mp ht
  refine ⟨hzero, g, hg, ?_⟩
  intro x
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (List.map_inj_left.mp he (relabel f x) (List.mem_finRange _)).symm

@[spectrum_native]
theorem row_chain : ∀ i : Fin 272, ∀ y, (row i y).val ≤ y.val + 1 := by native_decide

spectrum_assert covers complete
end Spectrum.SmallPairs.OrderThirteen
