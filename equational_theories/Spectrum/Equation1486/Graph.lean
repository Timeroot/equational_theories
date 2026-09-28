import equational_theories.Spectrum.Basic
import equational_theories.Equations.All
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-! Split-edge models of E1486. See `docs/1486_graph_spectrum.md`. -/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Spectrum.E1486

variable {A : Type*} [LinearOrder A]
variable (E : A → A → Prop) [DecidableRel E]

abbrev Point := (A × A) ⊕ {p : A × A // E p.1 p.2}

def first : Point E → A
  | .inl p => p.1
  | .inr p => p.val.1

def second : Point E → A
  | .inl p => p.2
  | .inr p => p.val.2

def kind : Point E → Bool
  | .inl p => decide (p.1 = p.2)
  | .inr _ => true

def marked : Point E → Option Bool
  | .inl p => if E p.1 p.2 then some (!(decide (p.1 < p.2))) else none
  | .inr p => some (decide (p.val.1 < p.val.2))

def select (a b : A) (t : Bool) : Point E :=
  if h : E a b then
    if decide (a < b) = t then .inr ⟨(a,b), h⟩ else .inl (a,b)
  else .inl (a,b)

def fallback (d : A → A) (a : A) (t : Bool) : Point E :=
  .inl (if t then (a,a) else (d a,a))

def op (d : A → A) (x y : Point E) : Point E :=
  let w := select E (second E x) (first E y) (kind E x)
  match marked E y with
  | none => w
  | some t => if kind E w = t then w else fallback E d (first E y) t

@[simp] theorem first_select (a b : A) (t : Bool) : first E (select E a b t) = a := by
  by_cases hab : E a b <;> by_cases ht : decide (a < b) = t <;> simp [select, hab, ht, first]

@[simp] theorem second_select (a b : A) (t : Bool) : second E (select E a b t) = b := by
  by_cases hab : E a b <;> by_cases ht : decide (a < b) = t <;> simp [select, hab, ht, second]

@[simp] theorem second_fallback (d : A → A) (a : A) (t : Bool) :
    second E (fallback E d a t) = a := by cases t <;> rfl

@[simp] theorem kind_fallback (d : A → A) (hd : ∀ a, d a ≠ a) (a : A) (t : Bool) :
    kind E (fallback E d a t) = t := by
  cases t <;> simp [fallback, kind, hd]

@[simp] theorem second_op (d : A → A) (x y : Point E) :
    second E (op E d x y) = first E y := by
  rw [op]
  split
  · simp
  · split <;> simp

theorem kind_op (d : A → A) (hd : ∀ a, d a ≠ a)
    (x y : Point E) (t : Bool) (hy : marked E y = some t) :
    kind E (op E d x y) = t := by
  simp only [op, hy]
  split
  · assumption
  · exact kind_fallback E d hd _ _

theorem select_marked (a b : A) (t u : Bool)
    (h : marked E (select E a b t) = some u) : u = t := by
  by_cases hab : E a b
  · simp only [select, dif_pos hab] at h
    cases hlt : decide (a < b) <;> cases t <;> cases u <;>
      simp [hlt, marked, hab] at h ⊢
  · simp [select, hab, marked] at h

theorem select_recover (hE : ∀ a, ¬ E a a) (x : Point E) (t : Bool)
    (ht : ∀ u, marked E x = some u → t = u) :
    select E (first E x) (second E x) t = x := by
  rcases x with ⟨a,b⟩ | ⟨⟨a,b⟩, hab⟩
  · by_cases hab : E a b
    · have hne : a ≠ b := by intro h; subst b; exact hE a hab
      have hh := ht (!(decide (a < b))) (by simp [marked, hab])
      simp only [first, second, select, dif_pos hab]
      rw [hh]
      simp
    · simp [first, second, select, hab]
  · have hh := ht (decide (a < b)) rfl
    simp [first, second, select, hab, hh]

theorem marked_fallback (hE : ∀ a, ¬ E a a)
    (d : A → A) (hdE : ∀ a, ¬ E (d a) a) (a : A) (t : Bool) :
    marked E (fallback E d a t) = none := by
  cases t <;> simp [fallback, marked, hE, hdE]

theorem square_unmarked (hE : ∀ a, ¬ E a a)
    (hsymm : ∀ a b, E a b → E b a)
    (d : A → A) (hdE : ∀ a, ¬ E (d a) a) (x : Point E) :
    marked E (op E d x x) = none := by
  rcases x with ⟨a,b⟩ | ⟨⟨a,b⟩, hab⟩
  · by_cases hab : E a b
    · have hba := hsymm a b hab
      have hne : a ≠ b := by intro h; subst b; exact hE a hab
      have hlt : b < a ↔ ¬a < b := by
        constructor
        · exact fun h => not_lt.mpr (le_of_lt h)
        · exact fun h => lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
      simp only [op, first, second, kind, marked, if_pos hab,
        decide_eq_false hne, select, dif_pos hba]
      by_cases ha : a < b <;> simp [ha, hlt, kind, marked, hab, hba,
        hne, Ne.symm hne, fallback, hE, hdE]
    · have hba : ¬ E b a := fun h => hab (hsymm b a h)
      simp [op, first, second, kind, marked, hab, hba, select]
  · have hba := hsymm a b hab
    have hne : a ≠ b := by intro h; subst b; exact hE a hab
    have hlt : b < a ↔ ¬a < b := by
      constructor
      · exact fun h => not_lt.mpr (le_of_lt h)
      · exact fun h => lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
    simp only [op, first, second, kind, marked, select, dif_pos hba]
    by_cases ha : a < b <;> simp [ha, hlt, kind, marked, hab, hba,
      hne, Ne.symm hne, fallback, hE, hdE]

theorem law (hE : ∀ a, ¬ E a a) (hsymm : ∀ a b, E a b → E b a)
    (d : A → A) (hd : ∀ a, d a ≠ a) (hdE : ∀ a, ¬ E (d a) a)
    (x y z : Point E) : op E d (op E d y x) (op E d x (op E d z z)) = x := by
  have hz := square_unmarked E hE hsymm d hdE z
  have hv : op E d x (op E d z z) =
      select E (second E x) (first E (op E d z z)) (kind E x) := by
    rw [op, hz]
  have hrec : select E (first E x) (second E x) (kind E (op E d y x)) = x :=
    select_recover E hE x _ (fun t ht => kind_op E d hd y x t ht)
  rw [hv]
  rw [op]
  rw [second_op, first_select, hrec]
  split
  · rfl
  · rename_i t ht
    have := select_marked E (second E x) (first E (op E d z z)) (kind E x) t ht
    simp [this]

@[implicit_reducible] def magma (d : A → A) : Magma (Point E) := ⟨op E d⟩

theorem hasModel [Fintype A] (hE : ∀ a, ¬ E a a)
    (hsymm : ∀ a b, E a b → E b a) (d : A → A)
    (hd : ∀ a, d a ≠ a) (hdE : ∀ a, ¬ E (d a) a) :
    Law1486.HasModel (Fintype.card A ^ 2 + Fintype.card {p : A × A // E p.1 p.2}) := by
  apply Law.MagmaLaw.hasModel_of_card (magma E d)
  · apply (@Law1486.models_iff _ (magma E d)).mpr
    intro x y z
    exact (law E hE hsymm d hd hdE x y z).symm
  · simp [Point, pow_two]

/-- info: 'Spectrum.E1486.hasModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasModel

end Spectrum.E1486
