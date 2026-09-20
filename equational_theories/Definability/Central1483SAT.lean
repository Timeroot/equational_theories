import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Std.Sat.CNF
import Std.Tactic.BVDecide.LRAT

set_option maxHeartbeats 2000000
open Std.Sat
namespace Magma.Central1483.CNF
variable {α β : Type*}
variable {n : Nat} [NeZero n]
abbrev Atom (n : Nat) := Fin 11 × Fin n × Fin n × Fin n
abbrev p (x y z : Fin n) : Atom n := (0,x,y,z)
abbrev row (x z : Fin n) : Atom n := (1,x,z,0)
abbrev good (x a b : Fin n) : Atom n := (2,x,a,b)
abbrev col (x z : Fin n) : Atom n := (3,x,z,0)
abbrev dual (x a b : Fin n) : Atom n := (4,x,a,b)
def rowSize (f : Fin n → Fin n → Fin n) (x : Fin n) : Nat :=
  (Finset.univ.filter (fun z => ∃ y, f x y = z)).card

def meaning (f : Fin n → Fin n → Fin n) (a : Atom n) : Bool :=
  match a.1.val with
  | 0 => decide (f a.2.1 a.2.2.1 = a.2.2.2)
  | 1 => decide (∃ z, f a.2.1 z = a.2.2.1)
  | 2 => decide (f a.2.2.1 (f a.2.1 a.2.2.2) = a.2.1)
  | 3 => decide (∃ z, f z a.2.1 = a.2.2.1)
  | 4 => decide (f (f a.2.2.2 a.2.1) a.2.2.1 = a.2.1)
  | 5 => decide (4 ≤ rowSize f a.2.1)
  | 7 => decide (3 ≤ rowSize f a.2.1)
  | 8 => decide (4 ≤ rowSize f a.2.1)
  | 10 => decide (6 ≤ rowSize f a.2.1)
  | _ => false

def all1 (F : Fin n → CNF α) : CNF α := ⟨(List.finRange n).toArray.flatMap (fun x => (F x).clauses)⟩
lemma sat_all1 (a : α → Bool) (F : Fin n → CNF α) (h : ∀ x, CNF.Sat a (F x)) :
    CNF.Sat a (all1 F) := by
  simp only [CNF.Sat, CNF.eval, all1, Array.all_flatMap, List.all_toArray, List.all_eq_true]
  intro x hx
  exact h x
lemma sat_single (a : α → Bool) (c : CNF.Clause α) (h : (CNF.Clause.eval a c) = true) :
    CNF.Sat a ⟨#[c]⟩ := by simpa [CNF.Sat, CNF.eval] using h
lemma sat_append (a : α → Bool) (F G : CNF α) (hF : CNF.Sat a F) (hG : CNF.Sat a G) :
    CNF.Sat a (F ++ G) := by simp_all [CNF.Sat]

def hasOutput : CNF (Atom n) := all1 fun x => all1 fun y =>
  ⟨#[(List.finRange n).map (fun z => (p x y z, true))]⟩
def uniqueOutput : CNF (Atom n) := all1 fun x => all1 fun y => all1 fun z => all1 fun w =>
  if z = w then .empty else ⟨#[[(p x y z,false),(p x y w,false)]]⟩
def rowPresent : CNF (Atom n) := all1 fun y => all1 fun z => all1 fun b =>
  ⟨#[[(p y z b,false),(row y b,true)]]⟩
def colPresent : CNF (Atom n) := all1 fun y => all1 fun z => all1 fun b =>
  ⟨#[[(p z y b,false),(col y b,true)]]⟩
def sourceInner : CNF (Atom n) := all1 fun x => all1 fun y => all1 fun a => all1 fun b =>
  ⟨#[[(p y x a,false),(row y b,false),(good x a b,true)]]⟩
def sourceOuter : CNF (Atom n) := all1 fun x => all1 fun a => all1 fun b => all1 fun c =>
  ⟨#[[(good x a b,false),(p x b c,false),(p a c x,true)]]⟩
def dualInner : CNF (Atom n) := all1 fun x => all1 fun y => all1 fun a => all1 fun b =>
  ⟨#[[(p x y a,false),(col y b,false),(dual x a b,true)]]⟩
def dualOuter : CNF (Atom n) := all1 fun x => all1 fun a => all1 fun b => all1 fun c =>
  ⟨#[[(dual x a b,false),(p b x c,false),(p c a x,true)]]⟩
def formula (n : Nat) [NeZero n] : CNF (Atom n) :=
  hasOutput ++ uniqueOutput ++ rowPresent ++ colPresent ++
  sourceInner ++ sourceOuter ++ dualInner ++ dualOuter

lemma model_hasOutput (f : Fin n → Fin n → Fin n) : CNF.Sat (meaning f) hasOutput := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_single
  simp only [CNF.Clause.eval, List.any_eq_true, List.mem_map]
  refine ⟨(p x y (f x y), true), ?_, ?_⟩
  · exact ⟨f x y, List.mem_finRange _, rfl⟩
  · simp [meaning, p]
lemma model_uniqueOutput (f : Fin n → Fin n → Fin n) : CNF.Sat (meaning f) uniqueOutput := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro z
  apply sat_all1; intro w
  split
  · exact CNF.sat_empty
  · apply sat_single
    by_cases hz : f x y = z <;> simp_all [CNF.Clause.eval, meaning, p]
lemma model_rowPresent (f : Fin n → Fin n → Fin n) : CNF.Sat (meaning f) rowPresent := by
  apply sat_all1; intro y
  apply sat_all1; intro z
  apply sat_all1; intro b
  apply sat_single
  by_cases hb : f y z = b
  · have h : ∃ t, f y t = b := ⟨z, hb⟩
    simp [CNF.Clause.eval, meaning, p, row, h]
  · simp [CNF.Clause.eval, meaning, p, row, hb]
lemma model_colPresent (f : Fin n → Fin n → Fin n) : CNF.Sat (meaning f) colPresent := by
  apply sat_all1; intro y
  apply sat_all1; intro z
  apply sat_all1; intro b
  apply sat_single
  by_cases hb : f z y = b
  · have h : ∃ t, f t y = b := ⟨z, hb⟩
    simp [CNF.Clause.eval, meaning, p, col, h]
  · simp [CNF.Clause.eval, meaning, p, col, hb]
lemma model_sourceInner (f : Fin n → Fin n → Fin n)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x) : CNF.Sat (meaning f) sourceInner := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_all1; intro b
  apply sat_single
  by_cases ha : f y x = a
  · by_cases hb : ∃ z, f y z = b
    · obtain ⟨z, hz⟩ := hb
      have hh : f a (f x b) = x := by simpa only [ha, hz] using h x y z
      simp [CNF.Clause.eval, meaning, p, row, good, hh]
    · simp [CNF.Clause.eval, meaning, p, row, good, hb]
  · simp [CNF.Clause.eval, meaning, p, row, good, ha]
lemma model_sourceOuter (f : Fin n → Fin n → Fin n) : CNF.Sat (meaning f) sourceOuter := by
  apply sat_all1; intro x
  apply sat_all1; intro a
  apply sat_all1; intro b
  apply sat_all1; intro c
  apply sat_single
  by_cases hc : f x b = c <;> simp [CNF.Clause.eval, meaning, p, good, hc]
lemma model_dualInner (f : Fin n → Fin n → Fin n)
    (h : ∀ x y z, f (f (f z y) x) (f x y) = x) : CNF.Sat (meaning f) dualInner := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_all1; intro b
  apply sat_single
  by_cases ha : f x y = a
  · by_cases hb : ∃ z, f z y = b
    · obtain ⟨z, hz⟩ := hb
      have hh : f (f b x) a = x := by simpa only [ha, hz] using h x y z
      simp [CNF.Clause.eval, meaning, p, col, dual, hh]
    · simp [CNF.Clause.eval, meaning, p, col, dual, hb]
  · simp [CNF.Clause.eval, meaning, p, col, dual, ha]
lemma model_dualOuter (f : Fin n → Fin n → Fin n) : CNF.Sat (meaning f) dualOuter := by
  apply sat_all1; intro x
  apply sat_all1; intro a
  apply sat_all1; intro b
  apply sat_all1; intro c
  apply sat_single
  by_cases hc : f b x = c <;> simp [CNF.Clause.eval, meaning, p, dual, hc]
lemma model_formula (f : Fin n → Fin n → Fin n)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (hd : ∀ x y z, f (f (f z y) x) (f x y) = x) : CNF.Sat (meaning f) (formula n) := by
  simp only [formula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨model_hasOutput f, model_uniqueOutput f⟩, model_rowPresent f⟩, model_colPresent f⟩, model_sourceInner f h⟩, model_sourceOuter f⟩, model_dualInner f hd⟩, model_dualOuter f⟩
def code (a : Atom n) : Nat := ((a.1.val*n+a.2.1.val)*n+a.2.2.1.val)*n+a.2.2.2.val
def sanitize (F : CNF Nat) : CNF Nat :=
  ⟨F.clauses.filter (fun c => !(c.any (fun l => c.contains (l.1, !l.2))))⟩
lemma sat_sanitize (F : CNF Nat) (a : Nat → Bool) (h : F.Sat a) : (sanitize F).Sat a := by
  simp only [CNF.Sat, CNF.eval, Array.all_eq_true_iff_forall_mem] at h ⊢
  intro c hc
  exact h c (Array.mem_filter.mp hc).1
lemma unsat_of_sanitize (F : CNF Nat) (h : (sanitize F).Unsat) : F.Unsat := by
  intro a
  cases he : F.eval a with
  | false => rfl
  | true =>
    have hs := sat_sanitize F a he
    have hn := h a
    rw [hs] at hn
    contradiction
def natFormula (n : Nat) [NeZero n] : CNF Nat := sanitize ((formula n).relabel code)
lemma no_model_of_unsat (hi : Function.Injective (@code n))
    (hn : (natFormula n).Unsat) (f : Fin n → Fin n → Fin n)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (hd : ∀ x y z, f (f (f z y) x) (f x y) = x) : False := by
  have hn' : (formula n).Unsat := (CNF.unsat_relabel_iff (fun _ _ he => hi he)).mp (unsat_of_sanitize _ hn)
  have hh := hn' (meaning f)
  rw [model_formula f h hd] at hh
  contradiction


end Magma.Central1483.CNF
namespace Magma.Central1483.Cardinality

lemma exists_mem_of_card (n k : Nat) (S : Finset (Fin n)) (hS : k ≤ S.card)
    (L : List (Fin n)) (hL : L.Nodup) (hl : L.length = n-k+1) :
    ∃ x ∈ L, x ∈ S := by
  classical
  by_contra hn
  push Not at hn
  have hd : Disjoint S L.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hl
    exact hn x (List.mem_toFinset.mp hl) hx
  have hc := Finset.card_le_card (Finset.subset_univ (S ∪ L.toFinset))
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ, Fintype.card_fin,
    List.toFinset_card_of_nodup hL, hl] at hc
  omega

lemma exists_not_mem_of_card (n k : Nat) (S : Finset (Fin n)) (hS : S.card ≤ k)
    (L : List (Fin n)) (hL : L.Nodup) (hl : L.length = k+1) :
    ∃ x ∈ L, x ∉ S := by
  classical
  by_contra hn
  push Not at hn
  have hs : L.toFinset ⊆ S := by
    intro x hx
    exact hn x (List.mem_toFinset.mp hx)
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hL, hl] at hc
  omega

end Magma.Central1483.Cardinality

namespace Magma.Central1483.CNF
variable {α β : Type*}
variable {n : Nat} [NeZero n]

def allList (L : List β) (F : β → CNF α) : CNF α :=
  ⟨L.toArray.flatMap (fun x => (F x).clauses)⟩
lemma sat_allList (a : α → Bool) (L : List β) (F : β → CNF α)
    (h : ∀ x ∈ L, CNF.Sat a (F x)) : CNF.Sat a (allList L F) := by
  simpa only [CNF.Sat, CNF.eval, allList, Array.all_flatMap, List.all_toArray,
    List.all_eq_true] using h

def combos (n k : Nat) : List (List (Fin n)) := ((List.finRange n).sublistsLen k).reverse
lemma combo_spec {L : List (Fin n)} {k : Nat} (h : L ∈ combos n k) :
    L.Nodup ∧ L.length = k := by
  have hh := List.mem_sublistsLen.mp (List.mem_reverse.mp h)
  exact ⟨hh.1.nodup (List.nodup_finRange n), hh.2⟩

def cardLower (im : Fin n → α) (k : Nat) : CNF α :=
  allList (combos n (n-k+1)) fun L => ⟨#[L.map (fun z => (im z, true))]⟩
def cardUpper (im : Fin n → α) (k : Nat) : CNF α :=
  allList (combos n (k+1)) fun L => ⟨#[L.map (fun z => (im z, false))]⟩
lemma sat_cardLower (a : α → Bool) (im : Fin n → α) (k : Nat) (S : Finset (Fin n))
    (hm : ∀ z, a (im z) = decide (z ∈ S)) (hc : k ≤ S.card) :
    CNF.Sat a (cardLower im k) := by
  apply sat_allList
  intro L hL
  obtain ⟨hd, hl⟩ := combo_spec hL
  obtain ⟨x, hx, hs⟩ := Magma.Central1483.Cardinality.exists_mem_of_card n k S hc L hd hl
  apply sat_single
  simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
  exact ⟨x, hx, by simp [hm, hs]⟩
lemma sat_cardUpper (a : α → Bool) (im : Fin n → α) (k : Nat) (S : Finset (Fin n))
    (hm : ∀ z, a (im z) = decide (z ∈ S)) (hc : S.card ≤ k) :
    CNF.Sat a (cardUpper im k) := by
  apply sat_allList
  intro L hL
  obtain ⟨hd, hl⟩ := combo_spec hL
  obtain ⟨x, hx, hs⟩ := Magma.Central1483.Cardinality.exists_not_mem_of_card n k S hc L hd hl
  apply sat_single
  simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
  exact ⟨x, hx, by simp [hm, hs]⟩

def guard (l : α × Bool) (F : CNF α) : CNF α := ⟨F.clauses.map (l :: ·)⟩
lemma sat_guard (a : α → Bool) (l : α × Bool) (F : CNF α)
    (h : a l.1 = l.2 ∨ CNF.Sat a F) : CNF.Sat a (guard l F) := by
  rcases h with h | h
  · simp [guard, CNF.Sat, CNF.eval, CNF.Clause.eval, h]
  · simp only [CNF.Sat, CNF.eval, guard, Array.all_map,
      Array.all_eq_true_iff_forall_mem] at h ⊢
    intro c hc
    simp only [Function.comp_apply, CNF.Clause.eval, List.any_cons, Bool.or_eq_true]
    exact Or.inr (h c hc)

end Magma.Central1483.CNF

namespace Magma.Central1483.CNF
variable {α β : Type*}
variable {n : Nat} [NeZero n]

def exactImages : CNF (Atom n) := all1 fun y => all1 fun b =>
  ⟨#[ (row y b, false) :: (List.finRange n).map (fun z => (p y z b, true)),
       (col y b, false) :: (List.finRange n).map (fun z => (p z y b, true)) ]⟩
def regularImages : CNF (Atom n) := all1 fun x => all1 fun b => all1 fun z =>
  ⟨#[[(col x b,false),(p x b z,false),(p z x b,true)],
      [(row x b,false),(p b x z,false),(p x z b,true)]]⟩
def nonfullImages : CNF (Atom n) := all1 fun x =>
  cardUpper (row x) (n-1) ++ cardUpper (col x) (n-1)
def minimumImages (k : Nat) : CNF (Atom n) := all1 fun x =>
  cardLower (row x) k ++ cardLower (col x) k

def normalizedImage (k : Nat) (zero : Bool) : CNF (Atom n) := all1 fun z =>
  ⟨#[[(row 0 z, if zero then decide (z.val < k) else decide (0 < z.val ∧ z.val ≤ k))]]⟩
def firstCell (zero : Bool) : CNF (Atom n) :=
  if zero then ⟨#[[(p 0 0 0,true),(p 0 0 1,true)]]⟩ else ⟨#[[(p 0 0 1,true)]]⟩
def large (x : Fin n) : Atom n := (5,x,0,0)
def rankThreeExtras : CNF (Atom n) :=
  (all1 fun x => guard (large x,false) (cardLower (row x) 4) ++
    guard (large x,false) (cardLower (col x) 4) ++
    ⟨#[[(p x x x,false),(large x,true)]]⟩) ++
  (all1 fun x => all1 fun y =>
    ⟨#[[(row x y,false),(large x,true),(large y,true)],
        [(col x y,false),(large x,true),(large y,true)]]⟩)
def sortedRow (k : Nat) : CNF (Atom n) := all1 fun y =>
  if k+1 ≤ y.val ∧ y.val < n-1 then
    all1 fun z => all1 fun w =>
      if z.val ≤ k ∧ w.val ≤ k ∧ w < z then
        ⟨#[[(p 0 y z,false),(p 0 (y+1) w,false)]]⟩ else .empty
  else .empty

def flag (threshold : Nat) (x : Fin n) : Atom n := (Fin.ofNat 11 (4+threshold),x,0,0)
def thresholdExtras : CNF (Atom n) :=
  (allList [3,4,6] fun t => all1 fun x =>
    guard (flag t x,false) (cardLower (row x) t) ++
    guard (flag t x,false) (cardLower (col x) t)) ++
  (all1 fun x => ⟨#[[(p x x x,false),(flag 4 x,true)]]⟩) ++
  (all1 fun x => all1 fun y => allList [row x y,col x y] fun edge =>
    allList [(3,6),(4,4),(6,3)] fun ts =>
      ⟨#[[(edge,false),(flag ts.1 x,true),(flag ts.2 y,true)]]⟩)

def rankFormula (n k : Nat) [NeZero n] (zero : Bool) : CNF (Atom n) :=
  formula n ++ exactImages ++ regularImages ++ nonfullImages ++ minimumImages k ++
  normalizedImage k zero ++ cardUpper (col 0) k ++ firstCell zero ++
  (if k=3 then rankThreeExtras else .empty) ++ sortedRow k ++ thresholdExtras

def natRankFormula (n k : Nat) [NeZero n] (zero : Bool) : CNF Nat :=
  sanitize ((rankFormula n k zero).relabel code)

lemma meaning_flag (f : Fin n → Fin n → Fin n) (t : Nat) (ht : t ∈ [3,4,6])
    (x : Fin n) : meaning f (flag t x) = decide (t ≤ rowSize f x) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> rfl

end Magma.Central1483.CNF

namespace Magma.Central1483.CNF
variable {α β : Type*}
variable {n : Nat} [NeZero n]

def rowSet (f : Fin n → Fin n → Fin n) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun z => ∃ y, f x y = z)
def colSet (f : Fin n → Fin n → Fin n) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun z => ∃ y, f y x = z)
lemma meaning_row (f : Fin n → Fin n → Fin n) (x z : Fin n) :
    meaning f (row x z) = decide (z ∈ rowSet f x) := by simp [meaning, row, rowSet]
lemma meaning_col (f : Fin n → Fin n → Fin n) (x z : Fin n) :
    meaning f (col x z) = decide (z ∈ colSet f x) := by simp [meaning, col, colSet]
lemma rowSize_eq (f : Fin n → Fin n → Fin n) (x : Fin n) :
    rowSize f x = (rowSet f x).card := rfl

structure RankAssumptions (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool) : Prop where
  source : ∀ x y z, f (f y x) (f x (f y z)) = x
  dual : ∀ x y z, f (f (f z y) x) (f x y) = x
  leftRegular : ∀ x y, f x (f (f x y) x) = f x y
  rightRegular : ∀ x y, f (f x (f y x)) x = f y x
  cardEq : ∀ x, (colSet f x).card = rowSize f x
  minimum : ∀ x, k ≤ rowSize f x
  nonfull : ∀ x, rowSize f x < 11
  rankZero : rowSize f 0 = k
  imageZero : ∀ z, (∃ y, f 0 y = z) ↔
    if zero then z.val < k else 0 < z.val ∧ z.val ≤ k
  first : if zero then f 0 0 = 0 ∨ f 0 0 = 1 else f 0 0 = 1
  sorted : ∀ y : Fin 11, k+1 ≤ y.val → y.val < 10 → f 0 y ≤ f 0 (y+1)
  idemRank : ∀ x, f x x = x → 4 ≤ rowSize f x
  rowRank : ∀ x y, 11 ≤ rowSize f x * rowSize f (f x y)
  colRank : ∀ x y, 11 ≤ rowSize f x * rowSize f (f y x)

lemma sat_two (a : α → Bool) (c d : CNF.Clause α)
    (hc : c.eval a = true) (hd : d.eval a = true) : CNF.Sat a ⟨#[c,d]⟩ := by
  simp [CNF.Sat, CNF.eval, hc, hd]

lemma model_exactImages (f : Fin n → Fin n → Fin n) :
    CNF.Sat (meaning f) exactImages := by
  apply sat_all1; intro y
  apply sat_all1; intro b
  apply sat_two
  · by_cases hb : ∃ z, f y z = b
    · obtain ⟨z, hz⟩ := hb
      simp only [CNF.Clause.eval, List.any_cons, Bool.or_eq_true]
      right
      simp only [List.any_map, List.any_eq_true]
      exact ⟨z, List.mem_finRange _, by simp [meaning, p, hz]⟩
    · simp [CNF.Clause.eval, meaning, row, hb]
  · by_cases hb : ∃ z, f z y = b
    · obtain ⟨z, hz⟩ := hb
      simp only [CNF.Clause.eval, List.any_cons, Bool.or_eq_true]
      right
      simp only [List.any_map, List.any_eq_true]
      exact ⟨z, List.mem_finRange _, by simp [meaning, p, hz]⟩
    · simp [CNF.Clause.eval, meaning, col, hb]

lemma model_regularImages (f : Fin n → Fin n → Fin n)
    (hl : ∀ x y, f x (f (f x y) x) = f x y)
    (hr : ∀ x y, f (f x (f y x)) x = f y x) :
    CNF.Sat (meaning f) regularImages := by
  apply sat_all1; intro x
  apply sat_all1; intro b
  apply sat_all1; intro z
  apply sat_two
  · by_cases hb : ∃ y, f y x = b
    · obtain ⟨y, hy⟩ := hb
      by_cases hz : f x b = z
      · have he : f z x = b := by simpa only [hy, hz] using hr x y
        simp [CNF.Clause.eval, meaning, p, col, he]
      · simp [CNF.Clause.eval, meaning, p, col, hz]
    · simp [CNF.Clause.eval, meaning, p, col, hb]
  · by_cases hb : ∃ y, f x y = b
    · obtain ⟨y, hy⟩ := hb
      by_cases hz : f b x = z
      · have he : f x z = b := by simpa only [hy, hz] using hl x y
        simp [CNF.Clause.eval, meaning, p, row, he]
      · simp [CNF.Clause.eval, meaning, p, row, hz]
    · simp [CNF.Clause.eval, meaning, p, row, hb]

lemma model_nonfullImages (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) nonfullImages := by
  apply sat_all1; intro x
  apply sat_append
  · apply sat_cardUpper _ _ _ (rowSet f x) (meaning_row f x)
    have := h.nonfull x
    change rowSize f x ≤ 11-1
    omega
  · apply sat_cardUpper _ _ _ (colSet f x) (meaning_col f x)
    rw [h.cardEq]
    have := h.nonfull x
    omega
lemma model_minimumImages (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) (minimumImages k) := by
  apply sat_all1; intro x
  apply sat_append
  · exact sat_cardLower _ _ _ (rowSet f x) (meaning_row f x) (h.minimum x)
  · apply sat_cardLower _ _ _ (colSet f x) (meaning_col f x)
    rw [h.cardEq]
    exact h.minimum x
lemma model_normalizedImage (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) (normalizedImage k zero) := by
  apply sat_all1; intro z
  apply sat_single
  have he := h.imageZero z
  cases zero <;> simp_all [CNF.Clause.eval, meaning, row]
lemma model_firstCell (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) (firstCell zero) := by
  have he := h.first
  cases zero <;> simp_all [firstCell, CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p]
lemma model_sortedRow (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) (sortedRow k) := by
  apply sat_all1; intro y
  split
  · rename_i hy
    apply sat_all1; intro z
    apply sat_all1; intro w
    split
    · rename_i hzw
      apply sat_single
      by_cases hz : f 0 y = z
      · have hn : f 0 (y+1) ≠ w := by
          intro hw
          have hs := h.sorted y hy.1 hy.2
          rw [hz,hw] at hs
          exact (not_le.mpr hzw.2.2) hs
        simp [CNF.Clause.eval, meaning, p, hn]
      · simp [CNF.Clause.eval, meaning, p, hz]
    · exact CNF.sat_empty
  · exact CNF.sat_empty

end Magma.Central1483.CNF

namespace Magma.Central1483.CNF
variable {α β : Type*}

lemma rank_threshold_disjunction (r s t u : Nat) (hn : 11 ≤ r*s)
    (ht : (t,u) ∈ [(3,6),(4,4),(6,3)]) : t ≤ r ∨ u ≤ s := by
  by_contra h
  push Not at h
  have hr : r ≤ t-1 := by omega
  have hs : s ≤ u-1 := by omega
  have hm := Nat.mul_le_mul hr hs
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
  rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num at hm <;> omega

lemma model_guarded_lower (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) (t : Nat) (ht : t ∈ [3,4,6]) (x : Fin 11) :
    CNF.Sat (meaning f) (guard (flag t x,false) (cardLower (row x) t) ++
      guard (flag t x,false) (cardLower (col x) t)) := by
  by_cases hx : t ≤ rowSize f x
  · apply sat_append
    · apply sat_guard
      right
      exact sat_cardLower _ _ _ (rowSet f x) (meaning_row f x) hx
    · apply sat_guard
      right
      apply sat_cardLower _ _ _ (colSet f x) (meaning_col f x)
      rw [h.cardEq]
      exact hx
  · apply sat_append <;> apply sat_guard <;> left <;>
      simp [meaning_flag f t ht, hx]

lemma model_thresholdExtras (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) thresholdExtras := by
  apply sat_append
  · apply sat_append
    · apply sat_allList
      intro t ht
      apply sat_all1; intro x
      exact model_guarded_lower f k zero h t ht x
    · apply sat_all1; intro x
      apply sat_single
      by_cases hi : f x x = x
      · have hr := h.idemRank x hi
        simp [CNF.Clause.eval, meaning, p, flag, hr]
      · simp [CNF.Clause.eval, meaning, p, flag, hi]
  · apply sat_all1; intro x
    apply sat_all1; intro y
    apply sat_allList; intro edge he
    apply sat_allList; intro ts hts
    have ht : ts.1 ∈ [3,4,6] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hts ⊢
      rcases hts with rfl | rfl | rfl <;> simp
    have hu : ts.2 ∈ [3,4,6] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hts ⊢
      rcases hts with rfl | rfl | rfl <;> simp
    apply sat_single
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · by_cases hy : ∃ z, f x z = y
      · obtain ⟨z,hz⟩ := hy
        have hb : 11 ≤ rowSize f x * rowSize f y := by simpa only [hz] using h.rowRank x z
        have hd := rank_threshold_disjunction _ _ _ _ hb hts
        rcases hd with hd | hd <;>
          simp [CNF.Clause.eval, meaning_flag f _ ht, meaning_flag f _ hu, hd]
      · simp [CNF.Clause.eval, meaning, row, hy]
    · by_cases hy : ∃ z, f z x = y
      · obtain ⟨z,hz⟩ := hy
        have hb : 11 ≤ rowSize f x * rowSize f y := by simpa only [hz] using h.colRank x z
        have hd := rank_threshold_disjunction _ _ _ _ hb hts
        rcases hd with hd | hd <;>
          simp [CNF.Clause.eval, meaning_flag f _ ht, meaning_flag f _ hu, hd]
      · simp [CNF.Clause.eval, meaning, col, hy]

lemma model_rankThreeExtras (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) rankThreeExtras := by
  apply sat_append
  · apply sat_all1; intro x
    apply sat_append
    · by_cases hx : 4 ≤ rowSize f x
      · apply sat_append
        · apply sat_guard
          right
          exact sat_cardLower _ _ _ (rowSet f x) (meaning_row f x) hx
        · apply sat_guard
          right
          apply sat_cardLower _ _ _ (colSet f x) (meaning_col f x)
          rw [h.cardEq]
          exact hx
      · apply sat_append <;> apply sat_guard <;> left <;> simp [meaning, large, hx]
    · apply sat_single
      by_cases hi : f x x = x
      · have hr := h.idemRank x hi
        simp [CNF.Clause.eval, meaning, p, large, hr]
      · simp [CNF.Clause.eval, meaning, p, large, hi]
  · apply sat_all1; intro x
    apply sat_all1; intro y
    apply sat_two
    · by_cases hy : ∃ z, f x z = y
      · obtain ⟨z,hz⟩ := hy
        have hb : 11 ≤ rowSize f x * rowSize f y := by simpa only [hz] using h.rowRank x z
        have hd := rank_threshold_disjunction _ _ 4 4 hb (by simp)
        rcases hd with hd | hd <;> simp [CNF.Clause.eval, meaning, large, hd]
      · simp [CNF.Clause.eval, meaning, row, hy]
    · by_cases hy : ∃ z, f z x = y
      · obtain ⟨z,hz⟩ := hy
        have hb : 11 ≤ rowSize f x * rowSize f y := by simpa only [hz] using h.colRank x z
        have hd := rank_threshold_disjunction _ _ 4 4 hb (by simp)
        rcases hd with hd | hd <;> simp [CNF.Clause.eval, meaning, large, hd]
      · simp [CNF.Clause.eval, meaning, col, hy]

lemma model_rankFormula (f : Fin 11 → Fin 11 → Fin 11) (k : Nat) (zero : Bool)
    (h : RankAssumptions f k zero) : CNF.Sat (meaning f) (rankFormula 11 k zero) := by
  have hc : CNF.Sat (meaning f) (cardUpper (col 0) k) := by
    apply sat_cardUpper _ _ _ (colSet f 0) (meaning_col f 0)
    rw [h.cardEq, h.rankZero]
  have ht : CNF.Sat (meaning f) (if k=3 then rankThreeExtras else .empty) := by
    split
    · exact model_rankThreeExtras f k zero h
    · exact CNF.sat_empty
  simp only [rankFormula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨model_formula f h.source h.dual,
    model_exactImages f⟩, model_regularImages f h.leftRegular h.rightRegular⟩,
    model_nonfullImages f k zero h⟩, model_minimumImages f k zero h⟩,
    model_normalizedImage f k zero h⟩, hc⟩, model_firstCell f k zero h⟩, ht⟩,
    model_sortedRow f k zero h⟩, model_thresholdExtras f k zero h⟩

end Magma.Central1483.CNF

/-! Any operation with the proved rank properties satisfies the exact finite SAT encoding. -/

/-- info: 'Magma.Central1483.CNF.model_rankFormula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Magma.Central1483.CNF.model_rankFormula
