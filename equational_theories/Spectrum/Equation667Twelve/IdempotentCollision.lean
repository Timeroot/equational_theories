import equational_theories.Spectrum.Equation667Twelve.Encoding
import equational_theories.Spectrum.Equation667FixedSquare.Cases
import equational_theories.Spectrum.FiniteSearch.Pinned

namespace Spectrum.E667.Twelve
open RightIdentityTwelve (Holds meaning)
open Spectrum.FiniteSearch
open FixedSquare.Cases (table representative)
set_option maxRecDepth 65536

def collisionRows : List (Fin 77) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]

@[spectrum_native]
private theorem fixed_point_zero : ∀ i : Fin 77,
    (∃ x, table i x = x) → table i 0 = 0 := by native_decide

@[spectrum_native]
private theorem row_coverage : ∀ i : Fin 77,
    table i 0 = 0 → (∃ x, x ≠ 0 ∧ table i (table i x) = x) → i ∈ collisionRows := by
  native_decide

def rowUnits (r : Fin 12 → Fin 12) : List Entry :=
  (List.finRange 12).map (fun y => (0,y,r y))

def natRow (i : Fin 77) : Std.Sat.CNF ℕ :=
  natFormula 12 (Fin.elim0 : Fin 0 → Fin 12 × Fin 12) (rowUnits (table i))

theorem no_fixed_row (i : Fin 77) (hn : (natRow i).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) (hr : ∀ y, f 0 y = table i y) : False := by
  apply no_model 12 (Fin.elim0 : Fin 0 → Fin 12 × Fin 12) (rowUnits (table i))
    (fun u _ => ⟨u.1.isLt,u.2.1.isLt,u.2.2.isLt⟩) hn f h
  intro u hu
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hu
  exact hr y

/-- A collision over an idempotent puts another point in a one- or two-cycle
of its left translation. Conjugacy reduces this to 50 first-row shapes. -/
theorem normalize_idempotent_collision (f : Fin 12 → Fin 12 → Fin 12)
    (h : Holds f) (he : f 0 0 = 0) (x : Fin 12) (hx : x ≠ 0) (hs : f x x = 0) :
    ∃ i ∈ collisionRows, ∃ g : Fin 12 → Fin 12 → Fin 12,
      Holds g ∧ ∀ y, g 0 y = table i y := by
  let L : Equiv.Perm (Fin 12) := Equiv.ofBijective (f 0) (RightIdentityTwelve.left_bijective h 0)
  obtain ⟨i,hc⟩ := FixedSquare.Cases.exists_conjugate L
  have hzero : table i 0 = 0 := by
    obtain ⟨e,hec⟩ := isConj_iff.mp hc
    apply fixed_point_zero i
    refine ⟨e 0, ?_⟩
    have hh := congrArg (fun p : Equiv.Perm (Fin 12) => p (e 0)) hec
    have hL : L 0 = 0 := he
    change e (L (e.symm (e 0))) = table i (e 0) at hh
    simpa only [Equiv.symm_apply_apply,hL] using hh.symm
  obtain ⟨e,he0,hec⟩ := conjugate_fix_point L (representative i) 0 he hzero hc
  have ht (z : Fin 12) : table i (e z) = e (L z) := by
    simpa only [Equiv.symm_apply_apply] using (hec (e z)).symm
  have htwo : L (L x) = x := by
    letI : Magma (Fin 12) := ⟨f⟩
    exact (square_fiber_iff (fun a b => (h a b).symm) 0 he x).mp hs
  have hi : i ∈ collisionRows := by
    apply row_coverage i hzero
    refine ⟨e x, ?_, ?_⟩
    · intro hh
      apply hx
      apply e.injective
      exact hh.trans he0.symm
    · rw [ht,ht,htwo]
  have hsym : e.symm 0 = 0 := by
    apply e.injective
    rw [Equiv.apply_symm_apply,he0]
  refine ⟨i,hi,relabel f e,RightIdentityTwelve.holds_relabel h e,?_⟩
  intro y
  simp only [relabel,hsym]
  exact hec y

theorem no_idempotent_collision_of_rows
    (hn : ∀ i ∈ collisionRows, (natRow i).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f)
    (he : f 0 0 = 0) (x : Fin 12) (hx : x ≠ 0) (hs : f x x = 0) : False := by
  obtain ⟨i,hi,g,hg,hr⟩ := normalize_idempotent_collision f h he x hx hs
  exact no_fixed_row i (hn i hi) g hg hr

spectrum_assert no_idempotent_collision_of_rows complete
end Spectrum.E667.Twelve
