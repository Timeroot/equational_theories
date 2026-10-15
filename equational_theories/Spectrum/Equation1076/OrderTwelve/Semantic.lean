import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Equation1076.OrderTwelve.PointData

/-! Semantic transfer between the finitely many symmetry-reduced cases.
No refutation or model-enumeration result is assumed here. -/
namespace Spectrum.E1076.OrderTwelve.Semantic
open Std.Sat SmallOrders SmallOrders.Encoding CanonicalData RowTransfer
open E63.OrderTen.Encoding (sat_append)

/-- Coverage supplies an actual row, rather than a trusted case enumeration. -/
theorem exists_row (hcover : coverage.Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1) : ∃ i : Fin 13, Matches f (row i) := by
  classical
  by_contra hn
  obtain ⟨a,ha,hval⟩ := RowTransfer.model_nat f h
    (fun _ x => ShortCycles.idempotent h x) hc
  have hall (i : Fin 13) : CNF.Clause.eval a ((units (row i)).map fun v => (v,false)) = true := by
    have he : ∃ y, f 0 y ≠ row i y := by
      by_contra he
      exact hn ⟨i,by simpa only [not_exists,not_not] using he⟩
    obtain ⟨y,hy⟩ := he
    simp only [CNF.Clause.eval,List.any_map,List.any_eq_true]
    refine ⟨code (p 0 y (row i y)), List.mem_map.mpr ⟨y,List.mem_finRange _,rfl⟩, ?_⟩
    simp [hval 0 y (row i y),hy]
  have hs : coverage.Sat a := by
    apply sat_append
    · exact ha
    simp only [CNF.Sat,CNF.eval,allRows,List.all_toArray,List.all_map,List.all_eq_true]
    exact fun i _ => hall i
  have hh := hcover a
  rw [hs] at hh
  contradiction

theorem transfer_row (i : Fin 13)
    (hn : ∀ g : Fin 12 → Fin 12 → Fin 12, Holds .e1076 g →
      Matches g (row (representative (target i))) → False)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hm : Matches f (row i)) : False := by
  let e := CanonicalData.permutation i
  have he : e 0 = 0 := CanonicalData.zero_fixed i
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let g (x y : Fin 12) := e (f (e.symm x) (e.symm y))
  apply hn g (holds_relabel h e)
  intro y
  simpa only [g,he',hm] using CanonicalData.conjugates i y

/-- Normalize a translation at any selected point, keeping its conjugacy explicit. -/
theorem normalize_at (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (x : Fin 12) : ∃ (g : Fin 12 → Fin 12 → Fin 12) (e : Equiv.Perm (Fin 12)),
      Holds .e1076 g ∧ e x = 0 ∧ (∀ a b, g (e a) (e b) = e (f a b)) ∧
      (∀ y, (g 0 y).val ≤ y.val + 1) := by
  let e₀ := Equiv.swap x 0
  let f₀ (a b : Fin 12) := e₀ (f (e₀.symm a) (e₀.symm b))
  obtain ⟨s,hs,hc⟩ := E63.OrderTen.exists_chain_label (f₀ 0)
  have hs' : s.symm 0 = 0 := by apply s.injective; simpa using hs.symm
  let e := e₀.trans s
  let g (a b : Fin 12) := e (f (e.symm a) (e.symm b))
  refine ⟨g,e,holds_relabel h e,?_,?_,?_⟩
  · simp [e,e₀,hs]
  · intro a b
    simp only [g,Equiv.symm_apply_apply]
  · intro y
    simpa only [g,e,Equiv.trans_apply,Equiv.symm_trans_apply,hs',f₀] using hc y

def allowed (j : Fin 6) : List (Fin 12) :=
  match j.val with
  | 0 => [2,3,4,7]
  | 1 | 2 => [2,3,4]
  | 3 => [2,3,4,5]
  | 4 => [2,3,4,5,6]
  | _ => [2,3,4,5,6,7,8,9,10,11]

private theorem point_allowed : ∀ j : Fin 6, ∀ z : Fin 12,
    z ≠ 0 → z ≠ 1 → PointData.point j z ∈ allowed j := by decide +kernel

/-- Preserve a canonical first row and choose an orbit representative for `f 1 0`. -/
theorem normalize_point (j : Fin 6)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hm : Matches f (row (representative j))) :
    ∃ g : Fin 12 → Fin 12 → Fin 12, Holds .e1076 g ∧
      Matches g (row (representative j)) ∧ g 1 0 ∈ allowed j := by
  let z := f 1 0
  let e := PointData.permutation j z
  have he0 : e 0 = 0 := PointData.zero_fixed j z
  have he1 : e 1 = 1 := PointData.one_fixed j z
  have he0' : e.symm 0 = 0 := by apply e.injective; simpa using he0.symm
  have he1' : e.symm 1 = 1 := by apply e.injective; simpa using he1.symm
  have hz0 : z ≠ 0 := by
    intro he
    have hh := (right_bijective h rfl 0).1 (he.trans (ShortCycles.idempotent h 0).symm)
    exact (by decide : (1 : Fin 12) ≠ 0) hh
  have hz1 : z ≠ 1 := by
    intro he
    have hh := (left_bijective h 1).1 (he.trans (ShortCycles.idempotent h 1).symm)
    exact (by decide : (0 : Fin 12) ≠ 1) hh
  let g (x y : Fin 12) := e (f (e.symm x) (e.symm y))
  refine ⟨g,holds_relabel h e,?_,?_⟩
  · intro y
    simpa only [g,he0',hm] using PointData.conjugates j z y
  · have hez : e z = PointData.point j z := PointData.maps_point j z
    change e (f (e.symm 1) (e.symm 0)) ∈ allowed j
    rw [he1',he0']
    change e z ∈ allowed j
    rw [hez]
    exact point_allowed j z hz0 hz1

/-- The final three row types have no three-cycle away from their fixed point. -/
theorem late_no_three : ∀ i : Fin 13, 3 ≤ (target i).val →
    ∀ z : Fin 12, z ≠ 0 → row i (row i (row i z)) ≠ z := by decide +kernel

end Spectrum.E1076.OrderTwelve.Semantic
