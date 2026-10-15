import equational_theories.Spectrum.Equation1076.OrderTwelve.RowTransfer

/-! Extra propagation constraints, and a distinguished entry in row one.
The three-cycle clauses are conditional: they are used only after the first
three translation types have been excluded by independent certificates. -/
namespace Spectrum.E1076.OrderTwelve.PointEncoding
open Std.Sat SmallOrders SmallOrders.Encoding CanonicalData
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)

abbrev NoThree (f : Fin 12 → Fin 12 → Fin 12) : Prop :=
  ∀ x y, x ≠ y → f x (f x (f x y)) ≠ y

def rowUnits (r : Row) : CNF (Atom 12) := all1 fun y => ⟨#[[(p 0 y (r y), true)]]⟩
def triangles : CNF (Atom 12) := all1 fun x => all1 fun y => all1 fun z =>
  if x ≠ y then ⟨#[[(p x y z,false),(p y z x,false)]]⟩ else .empty
def middleDiagonal : CNF (Atom 12) := all1 fun x => ⟨#[[(q x x x,true)]]⟩
def middleNotFixed : CNF (Atom 12) := all1 fun x => all1 fun y =>
  if x ≠ y then ⟨#[[(q x y x,false)]]⟩ else .empty
def threeCycles : CNF (Atom 12) := all1 fun x => all1 fun y => all1 fun a => all1 fun b =>
  if x ≠ y then ⟨#[[(p x y a,false),(p x a b,false),(p x b y,false)]]⟩ else .empty

def formula (r : Row) (cutThree : Bool) : CNF (Atom 12) :=
  ShortCycles.formula 12 ++ rowUnits r ++ triangles ++ middleDiagonal ++ middleNotFixed ++
    if cutThree then threeCycles else .empty

def natFormula (r : Row) (cutThree : Bool) : CNF ℕ :=
  sanitize ((formula r cutThree).relabel code)

def pointFormula (r : Row) (cutThree : Bool) (z : Fin 12) : CNF ℕ :=
  SmallOrders.CaseAssembly.caseFormula (natFormula r cutThree) [code (p 1 0 z)]

def groupFormula (r : Row) (cutThree : Bool) (zs : List (Fin 12)) : CNF ℕ :=
  natFormula r cutThree ++ ⟨#[(zs.map fun z => (code (p 1 0 z),true))]⟩

lemma model_rowUnits (f : Fin 12 → Fin 12 → Fin 12) (r : Row)
    (hm : RowTransfer.Matches f r) : (rowUnits r).Sat (meaning .e1076 f) := by
  apply sat_all1; intro y
  apply sat_single
  simp [CNF.Clause.eval,meaning,p,hm]

lemma model_triangles (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f) :
    triangles.Sat (meaning .e1076 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro z
  split
  · rename_i hxy
    apply sat_single
    by_cases he : f x y = z
    · have hh : f y z ≠ x := by simpa only [he] using ShortCycles.no_triangle h hxy
      simp [CNF.Clause.eval,meaning,p,hh]
    · simp [CNF.Clause.eval,meaning,p,he]
  · exact CNF.sat_empty

lemma model_middleDiagonal (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f) :
    middleDiagonal.Sat (meaning .e1076 f) := by
  apply sat_all1; intro x
  apply sat_single
  have hh : middle .e1076 f x x = x := by
    change f x (f x x) = x
    rw [ShortCycles.idempotent h, ShortCycles.idempotent h]
  simp [CNF.Clause.eval,meaning,q,hh]

lemma model_middleNotFixed (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f) :
    middleNotFixed.Sat (meaning .e1076 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  split
  · rename_i hxy
    apply sat_single
    have hh : middle .e1076 f x y ≠ x := by
      intro he
      have hd : middle .e1076 f x x = x := by
        change f x (f x x) = x
        rw [ShortCycles.idempotent h, ShortCycles.idempotent h]
      exact hxy ((ShortCycles.middle_left_bijective h x).1 (hd.trans he.symm))
    simp [CNF.Clause.eval,meaning,q,hh]
  · exact CNF.sat_empty

lemma model_threeCycles (f : Fin 12 → Fin 12 → Fin 12) (h3 : NoThree f) :
    threeCycles.Sat (meaning .e1076 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_all1; intro b
  split
  · rename_i hxy
    apply sat_single
    by_cases ha : f x y = a
    · by_cases hb : f x a = b
      · have hc : f x b ≠ y := by simpa only [ha,hb] using h3 x y hxy
        simp [CNF.Clause.eval,meaning,p,hc]
      · simp [CNF.Clause.eval,meaning,p,hb]
    · simp [CNF.Clause.eval,meaning,p,ha]
  · exact CNF.sat_empty

lemma model_formula (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (r : Row) (hm : RowTransfer.Matches f r) (hc : ∀ y, (r y).val ≤ y.val + 1)
    (cutThree : Bool) (h3 : cutThree = true → NoThree f) :
    (formula r cutThree).Sat (meaning .e1076 f) := by
  have hs := ShortCycles.model_formula f h (fun _ x => ShortCycles.idempotent h x)
    (fun y => by rw [hm]; exact hc y)
  have ht : (if cutThree then threeCycles else .empty).Sat (meaning .e1076 f) := by
    split
    · exact model_threeCycles f (h3 ‹_›)
    · exact CNF.sat_empty
  simp only [formula,CNF.Sat,CNF.eval_append,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨hs,model_rowUnits f r hm⟩,model_triangles f h⟩,
    model_middleDiagonal f h⟩,model_middleNotFixed f h⟩,ht⟩

lemma model_nat (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (r : Row) (hm : RowTransfer.Matches f r) (hc : ∀ y, (r y).val ≤ y.val + 1)
    (cutThree : Bool) (h3 : cutThree = true → NoThree f) :
    ∃ a : ℕ → Bool, (natFormula r cutThree).Sat a ∧
      ∀ x y z, a (code (p x y z)) = decide (f x y = z) := by
  classical
  let a : ℕ → Bool := Function.extend code (meaning .e1076 f) (fun _ => false)
  have ha : a ∘ code = meaning .e1076 f := Function.extend_comp code_injective _ _
  have hs : ((formula r cutThree).relabel code).Sat a := by
    apply CNF.sat_relabel
    rw [ha]
    exact model_formula f h r hm hc cutThree h3
  refine ⟨a, ?_, fun x y z => congrFun ha (p x y z)⟩
  simp only [CNF.Sat,CNF.eval,natFormula,sanitize,Array.all_eq_true_iff_forall_mem] at hs ⊢
  exact fun c hc => hs c (Array.mem_filter.mp hc).1

lemma no_row (r : Row) (cutThree : Bool) (hn : (natFormula r cutThree).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hm : RowTransfer.Matches f r) (hc : ∀ y, (r y).val ≤ y.val + 1)
    (h3 : cutThree = true → NoThree f) : False := by
  obtain ⟨a,ha,_⟩ := model_nat f h r hm hc cutThree h3
  have hh := hn a
  rw [ha] at hh
  contradiction

lemma no_point (r : Row) (cutThree : Bool) (z : Fin 12)
    (hn : (pointFormula r cutThree z).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hm : RowTransfer.Matches f r) (hc : ∀ y, (r y).val ≤ y.val + 1)
    (h3 : cutThree = true → NoThree f) (hz : f 1 0 = z) : False := by
  obtain ⟨a,ha,hval⟩ := model_nat f h r hm hc cutThree h3
  have hu : ∀ v ∈ [code (p 1 0 z)], a v = true := by
    intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    simp [hval,hz]
  have hs := SmallOrders.CaseAssembly.case_sat (natFormula r cutThree) _ a ha hu
  have hh := hn a
  change (SmallOrders.CaseAssembly.caseFormula (natFormula r cutThree)
    [code (p 1 0 z)]).eval a = false at hh
  rw [hs] at hh
  contradiction

lemma no_group (r : Row) (cutThree : Bool) (zs : List (Fin 12))
    (hn : (groupFormula r cutThree zs).Unsat)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hm : RowTransfer.Matches f r) (hc : ∀ y, (r y).val ≤ y.val + 1)
    (h3 : cutThree = true → NoThree f) (hz : f 1 0 ∈ zs) : False := by
  obtain ⟨a,ha,hval⟩ := model_nat f h r hm hc cutThree h3
  have hs : (groupFormula r cutThree zs).Sat a := by
    apply sat_append
    · exact ha
    apply sat_single
    simp only [CNF.Clause.eval,List.any_map,List.any_eq_true]
    exact ⟨f 1 0,hz,by simp [hval]⟩
  have hh := hn a
  rw [hs] at hh
  contradiction

end Spectrum.E1076.OrderTwelve.PointEncoding
