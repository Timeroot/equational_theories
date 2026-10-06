import equational_theories.Spectrum.Equation467.OrderSixteen.Rows
import equational_theories.Spectrum.Equation467Translations
import equational_theories.Spectrum.FiniteSearch.FirstUse

set_option maxRecDepth 4096
namespace Spectrum.E467.OrderSixteen
open FiniteSearch (relabel)

abbrev Holds (f : Point → Point → Point) : Prop :=
  ∀ x y, x = f y (f x (f x (f y y)))

theorem holds_relabel (f : Point → Point → Point) (h : Holds f)
    (e : Equiv.Perm Point) : Holds (relabel f e) := by
  intro x y
  simpa only [relabel, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
    congrArg e (h (e.symm x) (e.symm y))

def cycles (f : Point → Point) : ℕ → List Point → List (List Point)
  | 0, _ => []
  | _+1, [] => []
  | fuel+1, a::rest =>
    let orbit := a :: ((List.range 15).map (fun j => (f^[j+1]) a)).takeWhile (fun b => b != a)
    orbit :: cycles f fuel (rest.filter (fun b => !(orbit.contains b)))

def squareOrder (f : Point → Point) : List Point :=
  let cs := (cycles f 16 (List.finRange 16)).mergeSort (fun a b => a.length ≤ b.length)
  match cs.find? (fun c => 1 < c.length) with
  | none => cs.flatten
  | some first => first ++ (cs.filter (fun c => c != first)).flatten

def rowOrder (f : Point → Point) : List Point :=
  match cycles f 16 (List.finRange 16) with
  | [] => []
  | a::rest => a ++ ((rest.mergeSort (fun a b => a.length ≤ b.length)).flatten)

def orderPermutation (order : List Point) : Equiv.Perm Point :=
  ((List.finRange 16).zip order).foldl
    (fun r ab => r.trans (Equiv.swap ab.1 (r ab.2))) (Equiv.refl _)

def canonicalPermutation (isSquare : Bool) (f : Point → Point) : Equiv.Perm Point :=
  let table := ((List.finRange 16).map f).toArray
  let cached : Point → Point := fun x => table[x.val]!
  orderPermutation (if isSquare then squareOrder cached else rowOrder cached)

def squareRows : List (Point → Point) :=
  ((List.finRange 50).map fun i => axis ⟨i.val, by omega⟩) ++ [id]

def rowCases : List Case := (List.finRange 17).map fun i => ⟨50+i.val, by omega⟩

def squareAdmissible (f : Point → Point) : Prop :=
  (∀ x, f (f x) = x → f x = x) ∧ (∀ x, f (f (f x)) = x → f x = x)
instance (f : Point → Point) : Decidable (squareAdmissible f) := inferInstanceAs (Decidable (_ ∧ _))

def squareCorrect (f : Point → Point) : Bool :=
  if squareAdmissible f then
    let e := canonicalPermutation true f
    (squareRows.map (fun g => (List.finRange 16).map g)).contains
      ((List.finRange 16).map (fun x => e (f (e.symm x))))
  else true

@[spectrum_native]
theorem square_checked : (SmallPairs.ChainRows.rows 16 16).all squareCorrect = true := by
  native_decide

def rowAdmissible (f : Point → Point) : Prop :=
  (∀ x, f x = x ↔ x = 0) ∧ (∀ x, f (f x) = x → f x = x)
instance (f : Point → Point) : Decidable (rowAdmissible f) := inferInstanceAs (Decidable (_ ∧ _))

def rowCorrect (f : Point → Point) : Bool :=
  if rowAdmissible f then
    let e := canonicalPermutation false f
    decide (e 0 = 0) &&
      (rowCases.map (fun i => (List.finRange 16).map (axis i))).contains
        ((List.finRange 16).map (fun x => e (f (e.symm x))))
  else true

@[spectrum_native]
theorem row_checked : (SmallPairs.ChainRows.rows 16 16).all rowCorrect = true := by
  native_decide

theorem square_covers (f : Point → Point) (hi : Function.Injective f)
    (hc : ∀ x, (f x).val ≤ x.val+1) (ha : squareAdmissible f) :
    ∃ d ∈ squareRows, ∀ x, canonicalPermutation true f (f x) =
      d (canonicalPermutation true f x) := by
  have h := List.all_eq_true.mp square_checked f (SmallPairs.ChainRows.mem_rows f hi hc)
  simp only [squareCorrect, ha, ↓reduceIte, List.contains_iff_mem] at h
  obtain ⟨d, hd, he⟩ := List.mem_map.mp h
  refine ⟨d, hd, fun x => ?_⟩
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (List.map_inj_left.mp he (canonicalPermutation true f x) (List.mem_finRange _)).symm

theorem row_covers (f : Point → Point) (hi : Function.Injective f)
    (hc : ∀ x, (f x).val ≤ x.val+1) (ha : rowAdmissible f) :
    canonicalPermutation false f 0 = 0 ∧ ∃ i ∈ rowCases, ∀ x,
      canonicalPermutation false f (f x) = axis i (canonicalPermutation false f x) := by
  have h := List.all_eq_true.mp row_checked f (SmallPairs.ChainRows.mem_rows f hi hc)
  simp only [rowCorrect, ha, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at h
  obtain ⟨hz, ht⟩ := h
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ht
  refine ⟨hz, i, hi, fun x => ?_⟩
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (List.map_inj_left.mp he (canonicalPermutation false f x) (List.mem_finRange _)).symm

/-- The predicate subsequently preserved by the centralizer normalizations. -/
def InCase (i : Case) (f : Point → Point → Point) : Prop :=
  Holds f ∧ (∀ x, f x x = diagonal i x) ∧ (isIdempotent i = true → f 0 = axis i)

end Spectrum.E467.OrderSixteen
