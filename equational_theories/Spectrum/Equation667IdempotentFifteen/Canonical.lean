import equational_theories.Spectrum.Equation667IdempotentFifteen.Rows

set_option maxRecDepth 4096

namespace Spectrum.E667.IdempotentFifteen

def cycles (f : Fin 15 → Fin 15) : ℕ → List (Fin 15) → List (List (Fin 15))
  | 0, _ => []
  | _+1, [] => []
  | fuel+1, a::rest =>
    let orbit := a :: ((List.range 14).map (fun j => (f^[j+1]) a)).takeWhile (fun b => b != a)
    orbit :: cycles f fuel (rest.filter (fun b => !(orbit.contains b)))

def order (f : Fin 15 → Fin 15) : List (Fin 15) :=
  match cycles f 15 (List.finRange 15) with
  | [] => []
  | a::rest => a ++ ((rest.mergeSort (fun a b => a.length ≤ b.length)).flatten)

def relabel (f : Fin 15 → Fin 15) : Equiv.Perm (Fin 15) :=
  let table := ((List.finRange 15).map f).toArray
  let cached : Fin 15 → Fin 15 := fun x => table[x.val]!
  ((List.finRange 15).zip (order cached)).foldl
    (fun r ab => r.trans (Equiv.swap ab.1 (r ab.2))) (Equiv.refl _)

def admissible (f : Fin 15 → Fin 15) : Bool :=
  decide (f 0 = 0 ∧ ∀ x, f (f x) = x → x = 0)

def correct (f : Fin 15 → Fin 15) : Bool :=
  if !admissible f then true else
  let r := relabel f
  let table := (List.finRange 15).map (fun x => r (f (r.symm x)))
  decide (r 0 = 0) && (rows.map (fun g => (List.finRange 15).map g)).contains table

/-- This checks 16384 chain rows, whose exhaustive coverage is a general theorem.
It does not enumerate all permutations of fifteen elements. -/
@[spectrum_native]
theorem canonical_checked : (SmallPairs.ChainRows.rows 15 15).all correct = true := by
  native_decide

theorem covers (f : Fin 15 → Fin 15) (hi : Function.Injective f)
    (hc : ∀ i, (f i).val ≤ i.val + 1) (ha : admissible f = true) :
    relabel f 0 = 0 ∧ ∃ g ∈ rows, ∀ x, relabel f (f x) = g (relabel f x) := by
  have h := List.all_eq_true.mp canonical_checked f (SmallPairs.ChainRows.mem_rows f hi hc)
  simp only [correct, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨hzero, ht⟩ := h
  obtain ⟨g, hg, he⟩ := List.mem_map.mp ht
  refine ⟨hzero, g, hg, ?_⟩
  intro x
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (List.map_inj_left.mp he (relabel f x) (List.mem_finRange _)).symm

@[spectrum_native]
theorem row_chain : ∀ i : Fin 13, ∀ y, (row i y).val ≤ y.val + 1 := by native_decide

spectrum_assert covers complete
end Spectrum.E667.IdempotentFifteen
