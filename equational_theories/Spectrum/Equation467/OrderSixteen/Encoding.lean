import equational_theories.Spectrum.Equation467.OrderSixteen.Normalization
import equational_theories.Spectrum.Equation63.OrderTen.Encoding

namespace Spectrum.E467.OrderSixteen.Encoding
open Std.Sat
attribute [local irreducible] cells
open E63.OrderTen.Encoding (Atom p meaning all1 sat_all1 sat_single sat_append
  exactlyOne sat_exactlyOne latin code)

/-- Check complementary literals from the negative side only. This is linear
for the long first-use clauses, which have just one negative literal. -/
def sanitize (F : CNF ℕ) : CNF ℕ :=
  ⟨F.clauses.filter (fun c => !(c.any (fun l => !l.2 && c.contains (l.1, true))))⟩

/-- Concatenate clauses indexed by a finite list. -/
def allList {α β : Type} (xs : List α) (F : α → CNF β) : CNF β :=
  ⟨xs.toArray.flatMap fun x => (F x).clauses⟩

theorem sat_allList {α β : Type} (xs : List α) (F : α → CNF β) (m : β → Bool)
    (h : ∀ x ∈ xs, (F x).Sat m) : (allList xs F).Sat m := by
  simp only [CNF.Sat, CNF.eval, allList, Array.all_flatMap, List.all_toArray, List.all_eq_true]
  exact h

def diagonalClauses (i : Case) : CNF (Atom 16) := all1 fun x =>
  ⟨#[[(p x x (diagonal i x),true)],
     [(p x (diagonal i x) (inverseDiagonal i x),true)],
     [(p x (diagonal i (diagonal i x)) (diagonal i (diagonal i x)),true)]]⟩ ++
  (all1 fun y => if y ≠ diagonal i (diagonal i x) then ⟨#[[(p x y y,false)]]⟩ else .empty) ++
  (all1 fun y => all1 fun z => if y.val < z.val then
    ⟨#[[(p x y z,false),(p x z y,false)]]⟩ else .empty)

def triangles (i : Case) : CNF (Atom 16) := all1 fun x => all1 fun y =>
  let ry := inverseDiagonal i y
  all1 fun a => all1 fun b =>
  ⟨#[[(p x y a,false),(p x a b,false),(p ry b x,true)],
     [(p x y a,false),(p x a b,true),(p ry b x,false)],
     [(p x y a,true),(p x a b,false),(p ry b x,false)]]⟩

def rowUnits (i : Case) : CNF (Atom 16) :=
  if isIdempotent i then all1 fun y => ⟨#[[(p 0 y (axis i y),true)]]⟩ else .empty

def groupClause (i : Case) (y : Point) (r : Point × ℕ × Point) : CNF.Clause (Atom 16) :=
  (p (scanRow i) y r.2.2,false) ::
    ((List.finRange 16).filter fun j => j.val < y.val).flatMap fun j =>
      ((List.finRange 16).filter fun z => r.1.val ≤ z.val ∧ z.val < r.2.1).map
        fun z => (p (scanRow i) j z,true)

def groups (i : Case) : CNF (Atom 16) := all1 fun y =>
  if y.val < fixedCount i then allList (requests i) fun r => ⟨#[groupClause i y r]⟩ else .empty

def previous (z : Point) : Point := ⟨(z.val-1)%16,Nat.mod_lt _ (by decide)⟩

def fullClause (i : Case) (j : Fin 256) (z : Point) : CNF.Clause (Atom 16) :=
  (p (cells i j).1 (cells i j).2 z,false) ::
    ((List.finRange 256).filter fun t => t < j).map
      fun t => (p (cells i t).1 (cells i t).2 (previous z),true)

def full (i : Case) : CNF (Atom 16) :=
  if fullFirstUse i then all1 fun j => all1 fun z =>
    if fullBound i j < z.val then ⟨#[fullClause i j z]⟩ else .empty
  else .empty

def formula (i : Case) : CNF (Atom 16) :=
  latin ++ diagonalClauses i ++ triangles i ++ rowUnits i ++ groups i ++ full i

@[spectrum_native]
theorem inverse_checked : ∀ (i : Case) (x : Point),
    diagonal i (inverseDiagonal i x) = x := by native_decide

theorem model_latin (f : Point → Point → Point) (h : Holds f) : latin.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_append
  · apply sat_append
    · apply sat_exactlyOne
      · exact ⟨f x y, by simp [meaning]⟩
      · intro z w hz hw
        simp only [meaning, decide_eq_true_eq] at hz hw
        exact hz.symm.trans hw
    · apply sat_exactlyOne
      · obtain ⟨z,hz⟩ := Finite.surjective_of_injective (E467.left_injective f h x) y
        exact ⟨z,by simp [meaning,hz]⟩
      · intro z w hz hw
        simp only [meaning, decide_eq_true_eq] at hz hw
        exact E467.left_injective f h x (hz.trans hw.symm)
  · apply sat_exactlyOne
    · obtain ⟨z,hz⟩ := Finite.surjective_of_injective (E467.right_injective f h x) y
      exact ⟨z,by simp [meaning,hz]⟩
    · intro z w hz hw
      simp only [meaning, decide_eq_true_eq] at hz hw
      exact E467.right_injective f h x (hz.trans hw.symm)

theorem model_diagonal (i : Case) (f : Point → Point → Point) (hf : InCase i f) :
    (diagonalClauses i).Sat (meaning f) := by
  have h := hf.1
  have hd := hf.2.1
  have hroot (x : Point) : f x (diagonal i x) = inverseDiagonal i x := by
    have hh := E467.root_square f h (inverseDiagonal i x)
    change E467.root f (f _ _) = _ at hh
    rw [hd, inverse_checked] at hh
    simpa only [E467.root, E467.square, hd] using hh
  have hfixed (x y : Point) : f x y = y ↔ y = diagonal i (diagonal i x) := by
    simpa only [E467.square, hd] using E467.translation_fixed_iff f h x y
  apply sat_all1; intro x
  apply sat_append
  · apply sat_append
    · simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, hd, hroot,
        (hfixed x (diagonal i (diagonal i x))).mpr rfl]
    · apply sat_all1; intro y
      split
      · rename_i hy
        apply sat_single
        have he : f x y ≠ y := fun he => hy ((hfixed x y).mp he)
        simp [CNF.Clause.eval, meaning, p, he]
      · exact CNF.sat_empty
  · apply sat_all1; intro y
    apply sat_all1; intro z
    split
    · rename_i hyz
      apply sat_single
      by_cases he : f x y = z
      · have he' : f x z ≠ y := by
          intro he'
          have := congrArg Fin.val (E467.no_two_cycle f h x y z he he')
          omega
        simp [CNF.Clause.eval,meaning,p,he']
      · simp [CNF.Clause.eval,meaning,p,he]
    · exact CNF.sat_empty

theorem model_triangles (i : Case) (f : Point → Point → Point) (hf : InCase i f) :
    (triangles i).Sat (meaning f) := by
  have h := hf.1
  have recover (x y : Point) : f (inverseDiagonal i y) (f x (f x y)) = x := by
    simpa only [hf.2.1, inverse_checked] using (h x (inverseDiagonal i y)).symm
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_all1; intro b
  have hab (ha : f x y = a) (hb : f x a = b) : f (inverseDiagonal i y) b = x := by
    simpa only [ha,hb] using recover x y
  have hac (ha : f x y = a) (hc : f (inverseDiagonal i y) b = x) : f x a = b := by
    apply E467.left_injective f h (inverseDiagonal i y)
    simpa only [ha,hc] using recover x y
  have hbc (hb : f x a = b) (hc : f (inverseDiagonal i y) b = x) : f x y = a := by
    apply E467.left_injective f h x
    apply E467.left_injective f h (inverseDiagonal i y)
    simpa only [hb,hc] using recover x y
  by_cases ha : f x y = a <;> by_cases hb : f x a = b <;>
    by_cases hc : f (inverseDiagonal i y) b = x <;>
    simp_all [CNF.Sat,CNF.eval,CNF.Clause.eval,meaning,p]

theorem model_row (i : Case) (f : Point → Point → Point) (hf : InCase i f) :
    (rowUnits i).Sat (meaning f) := by
  unfold rowUnits
  split
  · rename_i hi
    apply sat_all1; intro y
    apply sat_single
    simp [CNF.Clause.eval,meaning,p,hf.2.2 hi]
  · exact CNF.sat_empty

theorem model_groups (i : Case) (f : Point → Point → Point) (hf : InCase i f)
    (hm : Minimal i f) : (groups i).Sat (meaning f) := by
  apply sat_all1; intro y
  split
  · rename_i hy
    apply sat_allList; intro r hr
    apply sat_single
    by_cases he : f (scanRow i) y = r.2.2
    · obtain ⟨j,hjy,hlo,hhi⟩ := minimal_groups i f hf hm y hy r hr he
      apply List.any_eq_true.mpr
      refine ⟨(p (scanRow i) j (f (scanRow i) j),true), ?_, by simp [meaning]⟩
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨j,by simpa only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] using hjy,?_⟩
      apply List.mem_map.mpr
      exact ⟨f (scanRow i) j,by simpa only [List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true, decide_eq_true_eq] using And.intro hlo hhi,rfl⟩
    · simp [CNF.Clause.eval,groupClause,meaning,p,he]
  · exact CNF.sat_empty

theorem model_full (i : Case) (f : Point → Point → Point) (hf : InCase i f)
    (hm : Minimal i f) : (full i).Sat (meaning f) := by
  unfold full
  split
  · rename_i hi
    apply sat_all1; intro j
    apply sat_all1; intro z
    split
    · rename_i hz
      apply sat_single
      by_cases he : f (cells i j).1 (cells i j).2 = z
      · obtain ⟨t,ht,hv⟩ := minimal_full i f hf hm hi j z hz he
        have hprev : f (cells i t).1 (cells i t).2 = previous z := by
          apply Fin.ext
          simpa only [previous, Nat.mod_eq_of_lt (show z.val-1 < 16 by have := z.isLt; omega)] using hv
        apply List.any_eq_true.mpr
        refine ⟨(p (cells i t).1 (cells i t).2 (previous z),true), ?_, by simp [meaning,hprev]⟩
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨t,by simp [ht],rfl⟩
      · simp [CNF.Clause.eval,fullClause,meaning,p,he]
    · exact CNF.sat_empty
  · exact CNF.sat_empty

theorem model_formula (i : Case) (f : Point → Point → Point) (hf : InCase i f)
    (hm : Minimal i f) : (formula i).Sat (meaning f) := by
  simp only [formula,CNF.Sat,CNF.eval_append,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨model_latin f hf.1,model_diagonal i f hf⟩,model_triangles i f hf⟩,
    model_row i f hf⟩,model_groups i f hf hm⟩,model_full i f hf hm⟩

theorem code16_injective : Function.Injective (@code 16) := by
  rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ he
  dsimp [code] at he
  have hz : z = z' := Fin.ext (by omega)
  have hy : y = y' := Fin.ext (by omega)
  have hx : x = x' := Fin.ext (by omega)
  exact Prod.ext hx (Prod.ext hy hz)

def natFormula (i : Case) : CNF ℕ := sanitize ((formula i).relabel code)

theorem impossible_of_unsat (i : Case) (f : Point → Point → Point)
    (hf : InCase i f) (hm : Minimal i f) (hu : (natFormula i).Unsat) : False := by
  have hu' : ((formula i).relabel code).Unsat := by
    intro a
    cases he : (((formula i).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natFormula i).Sat a := by
        simp only [CNF.Sat,CNF.eval,natFormula,sanitize,Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hu a
      rw [hs] at hh
      exact Bool.noConfusion hh
  have hraw := (CNF.unsat_relabel_iff (fun _ _ he => code16_injective he)).mp hu'
  have hh := hraw (meaning f)
  rw [model_formula i f hf hm] at hh
  contradiction

end Spectrum.E467.OrderSixteen.Encoding
