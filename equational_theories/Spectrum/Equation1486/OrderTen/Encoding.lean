import equational_theories.Spectrum.Equation1486.OrderTen.Normalization
import equational_theories.Spectrum.Equation63.OrderTen.Encoding

/-! Image-based one-hot encoding. Auxiliary atoms denote actual square,
column, and square-row images; every clause below is proved for every model. -/
namespace Spectrum.E1486.OrderTen.Encoding
open Std.Sat SquareRows
open E63.OrderTen.Encoding (all1 exactlyOne sat_all1 sat_single sat_append sat_exactlyOne sanitize)

inductive Atom where
  | p : Ten → Ten → Ten → Atom
  | squareAtom : Ten → Atom
  | col : Ten → Ten → Atom
  | r : Ten → Ten → Atom
  deriving DecidableEq
open Atom

def meaning (f : Ten → Ten → Ten) : Atom → Bool
  | p x y z => decide (f x y = z)
  | squareAtom s => decide (∃ z, f z z = s)
  | col x a => decide (∃ y, f y x = a)
  | r x b => decide (b ∈ row f x)

def code : Atom → ℕ
  | p x y z => (x.val * 10 + y.val) * 10 + z.val
  | squareAtom s => 1000 + s.val
  | col x a => 1010 + x.val * 10 + a.val
  | r x b => 1110 + x.val * 10 + b.val

theorem code_injective : Function.Injective code := by
  intro a b he
  cases a <;> cases b <;> simp only [code] at he <;>
    first | (congr 1 <;> apply Fin.ext <;> omega) | omega

def table : CNF Atom := all1 fun x => all1 fun y => exactlyOne (fun z => p x y z)
def squares : CNF Atom :=
  (all1 fun z => all1 fun s => ⟨#[[(p z z s,false),(squareAtom s,true)]]⟩) ++
  all1 fun s => ⟨#[[(squareAtom s,false)] ++ (List.finRange 10).map (fun z => (p z z s,true))]⟩
def rows : CNF Atom := all1 fun x => all1 fun s => all1 fun b =>
  ⟨#[[(squareAtom s,false),(p x s b,false),(r x b,true)]]⟩
def columns : CNF Atom := all1 fun x => all1 fun y => all1 fun a =>
  ⟨#[[(p y x a,false),(col x a,true)]]⟩
def law : CNF Atom := all1 fun x => all1 fun a => all1 fun b =>
  ⟨#[[(r x b,false),(col x a,false),(p a b x,true)]]⟩
def disjointRows : CNF Atom := all1 fun x => all1 fun a => all1 fun b => all1 fun u =>
  if a.val < b.val then ⟨#[[(r x a,false),(r x b,false),(r a u,false),(r b u,false)]]⟩
  else .empty
def two : CNF Atom := all1 fun x => all1 fun a =>
  ⟨#[(List.finRange 10).filterMap (fun b => if b ≠ a then some (r x b,true) else none)]⟩
def absorptionClauses : CNF Atom := all1 fun x => all1 fun y => all1 fun u =>
  ⟨#[[(r x y,false),(r y u,false),(p x u y,true)]]⟩
def involution : CNF Atom := all1 fun s => all1 fun t =>
  ⟨#[[(squareAtom s,false),(p s s t,false),(p t t s,true)]]⟩
def base : CNF Atom := table ++ squares ++ rows ++ columns ++ law ++ disjointRows ++
  two ++ absorptionClauses ++ involution

def normalizeRow (x : Ten) (T : Finset Ten) : CNF Atom := all1 fun b =>
  ⟨#[[(r x b,decide (b ∈ T))]]⟩
def three : CNF Atom := all1 fun x => all1 fun a => all1 fun b =>
  if a.val < b.val then
    ⟨#[(List.finRange 10).filterMap
      (fun c => if c ≠ a ∧ c ≠ b then some (r x c,true) else none)]⟩ else .empty

def small (inside : Bool) : CNF Atom := base ++ normalizeRow 0 (target 2 inside)
def large (inside : Bool) : CNF Atom := base ++ normalizeRow 0 (target 3 inside) ++ three

def noIdem (inside : Bool) : CNF Atom := large inside ++ ⟨#[[(squareAtom 0,true)]]⟩ ++
  (all1 fun x => ⟨#[[(p x x x,false)]]⟩) ++
  ⟨#[[(p 0 0 1,true)],[(p 1 1 0,true)]]⟩
def idem : CNF Atom := large true ++ ⟨#[[(p 0 0 0,true)]]⟩ ++
  normalizeRow 1 B1 ++ normalizeRow 2 B2

lemma model_table (f : Ten → Ten → Ten) : table.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_exactlyOne
  · exact ⟨f x y,by simp [meaning]⟩
  · intro z w hz hw
    simp only [meaning,decide_eq_true_eq] at hz hw
    exact hz.symm.trans hw

lemma model_squares (f : Ten → Ten → Ten) : squares.Sat (meaning f) := by
  apply sat_append
  · apply sat_all1; intro z
    apply sat_all1; intro s
    apply sat_single
    by_cases hh : f z z = s
    · have he : ∃ z, f z z = s := ⟨z,hh⟩
      simp [CNF.Clause.eval,meaning,he]
    · simp [CNF.Clause.eval,meaning,hh]
  · apply sat_all1; intro s
    apply sat_single
    by_cases hh : ∃ z, f z z = s
    · obtain ⟨z,hz⟩ := hh
      simp only [CNF.Clause.eval,List.any_append,Bool.or_eq_true]
      right
      simp only [List.any_map,List.any_eq_true]
      exact ⟨z,List.mem_finRange _,by simpa [meaning] using hz⟩
    · simp [CNF.Clause.eval,meaning,hh]

lemma model_rows (f : Ten → Ten → Ten) : rows.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro s
  apply sat_all1; intro b
  apply sat_single
  have hh (hs : ∃ z, f z z = s) (hb : f x s = b) : b ∈ row f x := by
    obtain ⟨z,rfl⟩ := hs
    exact (mem_row f x b).mpr ⟨z,hb⟩
  by_cases hs : ∃ z, f z z = s <;> by_cases hb : f x s = b <;>
    simp_all [CNF.Clause.eval,meaning]

lemma model_columns (f : Ten → Ten → Ten) : columns.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_single
  by_cases hh : f y x = a
  · have he : ∃ y, f y x = a := ⟨y,hh⟩
    simp [CNF.Clause.eval,meaning,he]
  · simp [CNF.Clause.eval,meaning,hh]

lemma model_law (f : Ten → Ten → Ten) (h : Lawful f) : law.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro a
  apply sat_all1; intro b
  apply sat_single
  have hh (hr : b ∈ row f x) (hc : ∃ y, f y x = a) : f a b = x := by
    obtain ⟨z,rfl⟩ := (mem_row f x b).mp hr
    obtain ⟨y,rfl⟩ := hc
    exact h x y z
  by_cases hr : b ∈ row f x <;> by_cases hc : ∃ y, f y x = a <;>
    simp_all [CNF.Clause.eval,meaning]

lemma model_disjoint (f : Ten → Ten → Ten) (h : Lawful f) :
    disjointRows.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro a
  apply sat_all1; intro b
  apply sat_all1; intro u
  split
  · rename_i hab
    apply sat_single
    have hh : ¬ (a ∈ row f x ∧ b ∈ row f x ∧ u ∈ row f a ∧ u ∈ row f b) := by
      rintro ⟨ha,hb,hu,hv⟩
      exact Finset.disjoint_left.mp (row_disjoint f h x ha hb
        (by intro he; subst b; omega)) hu hv
    by_cases ha : a ∈ row f x <;> by_cases hb : b ∈ row f x <;>
      by_cases hu : u ∈ row f a <;> simp_all [CNF.Clause.eval,meaning]
  · exact CNF.sat_empty

lemma avoid (S T : Finset Ten) (h : T.card < S.card) : ∃ b ∈ S, b ∉ T := by
  apply Finset.not_subset.mp
  intro hs
  have := Finset.card_le_card hs
  omega

lemma model_two (f : Ten → Ten → Ten) (h : Lawful f) : two.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro a
  apply sat_single
  obtain ⟨b,hb,hba⟩ := avoid (row f x) {a} (by
    simpa using two_le_row_card f h x)
  simp only [Finset.mem_singleton] at hba
  simp only [CNF.Clause.eval,List.any_filterMap,List.any_eq_true]
  exact ⟨b,List.mem_finRange _,by simp [hba,meaning,hb]⟩

lemma model_absorption (f : Ten → Ten → Ten) (h : Lawful f) :
    absorptionClauses.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro u
  apply sat_single
  have hh (hy : y ∈ row f x) (hu : u ∈ row f y) : f x u = y :=
    return_on_row f h x y hy u hu
  by_cases hy : y ∈ row f x <;> by_cases hu : u ∈ row f y <;>
    simp_all [CNF.Clause.eval,meaning]

lemma model_involution (f : Ten → Ten → Ten) (h : Lawful f) :
    involution.Sat (meaning f) := by
  apply sat_all1; intro s
  apply sat_all1; intro t
  apply sat_single
  have hh (hs : ∃ z, f z z = s) (ht : f s s = t) : f t t = s := by
    obtain ⟨z,rfl⟩ := hs
    simpa only [ht] using square_tripotent f h z
  by_cases hs : ∃ z, f z z = s <;> by_cases ht : f s s = t <;>
    simp_all [CNF.Clause.eval,meaning]

lemma model_base (f : Ten → Ten → Ten) (h : Lawful f) : base.Sat (meaning f) := by
  simp only [base,CNF.Sat,CNF.eval_append,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨model_table f,model_squares f⟩,model_rows f⟩,model_columns f⟩,
    model_law f h⟩,model_disjoint f h⟩,model_two f h⟩,model_absorption f h⟩,model_involution f h⟩

lemma model_normalizeRow (f : Ten → Ten → Ten) (x : Ten) (T : Finset Ten)
    (ht : row f x = T) : (normalizeRow x T).Sat (meaning f) := by
  apply sat_all1; intro b
  apply sat_single
  simp only [CNF.Clause.eval,meaning]
  simp
  rw [← mem_row,ht]

lemma model_three (f : Ten → Ten → Ten) (h : ∀ x, (row f x).card = 3) :
    three.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro a
  apply sat_all1; intro b
  split
  · apply sat_single
    obtain ⟨c,hc,hcab⟩ := avoid (row f x) {a,b} (by
      rw [h]; have hh := Finset.card_insert_le a {b}; simp only [Finset.card_singleton] at hh; omega)
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hcab
    simp only [CNF.Clause.eval,List.any_filterMap,List.any_eq_true]
    exact ⟨c,List.mem_finRange _,by simp [hcab,meaning,hc]⟩
  · exact CNF.sat_empty


lemma model_small (f : Ten → Ten → Ten) (h : Lawful f) (inside : Bool)
    (hr : row f 0 = target 2 inside) : (small inside).Sat (meaning f) :=
  sat_append _ _ _ (model_base f h) (model_normalizeRow f 0 _ hr)

lemma model_large (f : Ten → Ten → Ten) (h : Lawful f) (inside : Bool)
    (hr : row f 0 = target 3 inside) (h3 : ∀ x, (row f x).card = 3) :
    (large inside).Sat (meaning f) :=
  sat_append _ _ _ (sat_append _ _ _ (model_base f h) (model_normalizeRow f 0 _ hr))
    (model_three f h3)

lemma model_noIdem (f : Ten → Ten → Ten) (h : Lawful f) (inside : Bool)
    (hr : row f 0 = target 3 inside) (h3 : ∀ x, (row f x).card = 3)
    (hs : ∃ z, f z z = 0) (hi : ∀ x, f x x ≠ x) (h01 : f 0 0 = 1)
    (h10 : f 1 1 = 0) : (noIdem inside).Sat (meaning f) := by
  apply sat_append
  · apply sat_append
    · apply sat_append
      · exact model_large f h inside hr h3
      · apply sat_single
        simp [CNF.Clause.eval,meaning,hs]
    · apply sat_all1; intro x
      apply sat_single
      simp [CNF.Clause.eval,meaning,hi]
  · simp [CNF.Sat,CNF.eval,CNF.Clause.eval,meaning,h01,h10]

lemma model_idem (f : Ten → Ten → Ten) (h : Lawful f)
    (hr : row f 0 = target 3 true) (h3 : ∀ x, (row f x).card = 3)
    (hi : f 0 0 = 0) (h1 : row f 1 = B1) (h2 : row f 2 = B2) :
    idem.Sat (meaning f) := by
  apply sat_append
  · apply sat_append
    · apply sat_append
      · exact model_large f h true hr h3
      · apply sat_single
        simp [CNF.Clause.eval,meaning,hi]
    · exact model_normalizeRow f 1 B1 h1
  · exact model_normalizeRow f 2 B2 h2

def toNat (F : CNF Atom) : CNF ℕ := sanitize (F.relabel code)

theorem no_model_of_unsat (F : CNF Atom) (hn : (toNat F).Unsat)
    (f : Ten → Ten → Ten) (hf : F.Sat (meaning f)) : False := by
  have hu : (F.relabel code).Unsat := by
    intro a
    cases he : (F.relabel code).eval a with
    | false => rfl
    | true =>
      have hs : (toNat F).Sat a := by
        simp only [CNF.Sat,CNF.eval,toNat,sanitize,Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hn a
      rw [hs] at hh
      contradiction
  have hn' := (CNF.unsat_relabel_iff (fun _ _ he => code_injective he)).mp hu
  have hh := hn' (meaning f)
  rw [hf] at hh
  contradiction

end Spectrum.E1486.OrderTen.Encoding
