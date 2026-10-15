import equational_theories.Spectrum.Equation1483.OrderTwelve.SecondLexNormalization
import equational_theories.Spectrum.Equation1483.OrderTwelve.CombinedEncoding

/-! Prefix flags for complete second-row symmetry inside first-row fibers.
The `full` variant follows the prefix through all twelve entries; otherwise
it stops at the first label moved by the transposition. -/
namespace Spectrum.E1483.OrderTwelve.SecondLexEncoding
open Std.Sat Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalization SecondLexNormalization
abbrev A := Fin 12
abbrev Op := A → A → A
abbrev Var := HeadLexEncoding.Var ⊕ (A × A × A)
def old (x : HeadLexEncoding.Var) : Var := .inl x
def atom (x : Atom 12) : Var := old (HeadLexEncoding.old x)
def flag (a b i : A) : Var := .inr (a,b,i)
def number : Var → Nat
  | .inl x => HeadLexEncoding.number x
  | .inr (a,b,i) => 22464+(a.val*12+b.val)*12+i.val

abbrev Guard (f : Op) (a b : A) : Prop :=
  (¬ ∃ x, f x 0 = a) ∧ (¬ ∃ x, f x 0 = b) ∧ f 0 a = f 0 b

def assignment (f : Op) : Var → Bool
  | .inl x => HeadLexEncoding.assignment f x
  | .inr (a,b,i) => decide (Guard f a b ∧ ∀ j : A, j < i → f 1 j = swapRow f a b j)

def cutoff (full : Bool) (a : A) : Nat := if full then 11 else a.val

def start (a b u : A) : CNF Var :=
  ⟨#[[(atom (col 0 a),true),(atom (col 0 b),true),(atom (p 0 a u),false),
    (atom (p 0 b u),false),(flag a b 0,true)]]⟩

def steps (full : Bool) (a b i v w : A) : CNF Var :=
  (if v > Equiv.swap a b w then
    ⟨#[[(flag a b i,false),(atom (p 1 i v),false),(atom (p 1 (Equiv.swap a b i) w),false)]]⟩
  else .empty) ++
  (if v = Equiv.swap a b w ∧ i.val < cutoff full a then
    ⟨#[[(flag a b i,false),(atom (p 1 i v),false),(atom (p 1 (Equiv.swap a b i) w),false),
      (flag a b (i+1),true)]]⟩
  else .empty)

def extras (full : Bool) (k : Nat) (zero : Bool) : CNF Var :=
  all1 fun a => all1 fun b =>
  if bound k zero < a.val ∧ a < b then
    (all1 fun u => if u.val ≤ k then start a b u else .empty) ++
    (all1 fun i => if i.val ≤ cutoff full a then all1 fun v => all1 fun w => steps full a b i v w
      else .empty)
  else .empty

def formula (full : Bool) (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Var :=
  (HeadLexEncoding.formula k zero cells).relabel old ++ extras full k zero

def strongFormula (full : Bool) (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Var :=
  (CombinedEncoding.formula k zero cells).relabel old ++ extras full k zero

def toNat (full : Bool) (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Nat :=
  sanitize ((formula full k zero cells).relabel number)

def strongNat (full : Bool) (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Nat :=
  sanitize ((strongFormula full k zero cells).relabel number)

lemma old_number_lt (x : HeadLexEncoding.Var) : HeadLexEncoding.number x < 22464 := by
  rcases x with x | ⟨a,b,i⟩
  · have ht := x.1.isLt
    have hx := x.2.1.isLt
    have hy := x.2.2.1.isLt
    have hz := x.2.2.2.isLt
    simp only [HeadLexEncoding.number,code]
    omega
  · have ha := a.isLt; have hb := b.isLt; have hi := i.isLt
    simp only [HeadLexEncoding.number]
    omega

lemma number_injective : Function.Injective number := by
  rintro (x|⟨a,b,i⟩) (y|⟨c,d,j⟩) he
  · exact congrArg Sum.inl (HeadLexEncoding.number_injective he)
  · have hx := old_number_lt x
    simp only [number] at he
    omega
  · have hy := old_number_lt y
    simp only [number] at he
    omega
  · simp only [number] at he
    have hi : i = j := Fin.ext (by omega)
    have hb : b = d := Fin.ext (by omega)
    have ha : a = c := Fin.ext (by omega)
    subst c; subst d; subst j
    rfl

lemma model_start (f : Op) (a b u : A) : CNF.Sat (assignment f) (start a b u) := by
  apply sat_single
  by_cases hca : ∃ x, f x 0 = a
  · simp [CNF.Clause.eval,assignment,atom,old,HeadLexEncoding.assignment,HeadLexEncoding.old,
      meaning,col,hca]
  by_cases hcb : ∃ x, f x 0 = b
  · simp [CNF.Clause.eval,assignment,atom,old,HeadLexEncoding.assignment,HeadLexEncoding.old,
      meaning,col,hcb]
  by_cases ha : f 0 a = u
  swap
  · simp [CNF.Clause.eval,assignment,atom,old,HeadLexEncoding.assignment,HeadLexEncoding.old,
      meaning,p,ha]
  by_cases hb : f 0 b = u
  swap
  · simp [CNF.Clause.eval,assignment,atom,old,HeadLexEncoding.assignment,HeadLexEncoding.old,
      meaning,p,hb]
  have hg : Guard f a b := ⟨hca,hcb,ha.trans hb.symm⟩
  have hf : assignment f (flag a b 0) = true := by
    change decide (Guard f a b ∧ ∀ j : A, j < 0 → f 1 j = swapRow f a b j) = true
    apply decide_eq_true
    exact ⟨hg,fun j hj => (Fin.not_lt_zero j hj).elim⟩
  simp [CNF.Clause.eval,hf]

lemma model_steps (f : Op) (full : Bool) (k : Nat) (zero : Bool)
    (hl : SecondLex f k zero) (a b i v w : A)
    (ha : bound k zero < a.val) (hab : a < b) :
    CNF.Sat (assignment f) (steps full a b i v w) := by
  have hbound : cutoff full a ≤ 11 := by cases full <;> simp [cutoff] <;> omega
  apply sat_append
  · split
    next hgt =>
      apply sat_single
      by_cases hp : Guard f a b ∧ ∀ j : A, j < i → f 1 j = swapRow f a b j
      swap
      · have hf : assignment f (flag a b i) = false := by
          change decide (Guard f a b ∧ ∀ j : A, j < i → f 1 j = swapRow f a b j) = false
          exact decide_eq_false hp
        simp [CNF.Clause.eval,hf]
      by_cases hv : f 1 i = v
      swap
      · simp [CNF.Clause.eval,assignment,atom,old,HeadLexEncoding.assignment,HeadLexEncoding.old,
          meaning,p,hv]
      by_cases hw : f 1 (Equiv.swap a b i) = w
      swap
      · simp [CNF.Clause.eval,assignment,atom,old,HeadLexEncoding.assignment,HeadLexEncoding.old,
          meaning,p,hw]
      have hh := hl a b i ha hab hp.1.1 hp.1.2.1 hp.1.2.2 hp.2
      simp only [swapRow,hv,hw] at hh
      exact (not_lt_of_ge hh hgt).elim
    next => exact CNF.sat_empty
  · split
    next he =>
      apply sat_single
      by_cases hp : Guard f a b ∧ ∀ j : A, j < i → f 1 j = swapRow f a b j
      swap
      · have hf : assignment f (flag a b i) = false := by
          change decide (Guard f a b ∧ ∀ j : A, j < i → f 1 j = swapRow f a b j) = false
          exact decide_eq_false hp
        simp [CNF.Clause.eval,hf]
      by_cases hv : f 1 i = v
      swap
      · simp [CNF.Clause.eval,assignment,atom,old,HeadLexEncoding.assignment,HeadLexEncoding.old,
          meaning,p,hv]
      by_cases hw : f 1 (Equiv.swap a b i) = w
      swap
      · simp [CNF.Clause.eval,assignment,atom,old,HeadLexEncoding.assignment,HeadLexEncoding.old,
          meaning,p,hw]
      have hnext : (i+1).val = i.val+1 := Fin.val_add_one_of_lt (by change i.val < 11; omega)
      have hp' : ∀ j : A, j < i+1 → f 1 j = swapRow f a b j := by
        intro j hj
        have hjv : j.val < i.val+1 := by change j.val < (i+1).val at hj; omega
        by_cases hji : j < i
        · exact hp.2 j hji
        have hej : j = i := Fin.ext (by change ¬ j.val < i.val at hji; omega)
        subst j
        simpa only [swapRow,hv,hw] using he.1
      have hflag : assignment f (flag a b (i+1)) = true := by
        simp only [assignment,flag,decide_eq_true_eq]
        exact ⟨hp.1,hp'⟩
      simp [CNF.Clause.eval,hflag]
    next => exact CNF.sat_empty

lemma model_extras (f : Op) (full : Bool) (k : Nat) (zero : Bool)
    (hl : SecondLex f k zero) : CNF.Sat (assignment f) (extras full k zero) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  split
  next h =>
    apply sat_append
    · apply sat_all1; intro u
      split
      next => exact model_start f a b u
      next => exact CNF.sat_empty
    · apply sat_all1; intro i
      split
      next =>
        apply sat_all1; intro v
        apply sat_all1; intro w
        exact model_steps f full k zero hl a b i v w h.1 h.2
      next => exact CNF.sat_empty
  next => exact CNF.sat_empty

lemma model_formula (f : Op) (full : Bool) (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (h : NormalForm f k zero) (hl : SecondLex f k zero)
    (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : CNF.Sat (assignment f) (formula full k zero cells) := by
  apply sat_append
  · apply CNF.sat_relabel
    simpa [Function.comp_def,assignment,old] using
      (HeadLexEncoding.model_formula k zero cells f h.bounds.2 h.core h.sorted
        (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex hc)
  · exact model_extras f full k zero hl

lemma model_strongFormula (f : Op) (full : Bool) (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (h : NormalForm f k zero) (hl : SecondLex f k zero)
    (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : CNF.Sat (assignment f) (strongFormula full k zero cells) := by
  apply sat_append
  · apply CNF.sat_relabel
    simpa [Function.comp_def,assignment,old] using
      (CombinedEncoding.model_formula f k zero cells h.bounds.2 h.core h.sorted
        (by simpa using h.chain 1) h.firstMention h.predecessor h.headLex h.chain hc)
  · exact model_extras f full k zero hl

lemma no_model (full : Bool) (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (hn : (toNat full k zero cells).Unsat) (f : Op) (h : NormalForm f k zero)
    (hl : SecondLex f k zero) (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False := by
  have hn' : (formula full k zero cells).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => number_injective he)).mp (unsat_of_sanitize _ hn)
  exact Bool.false_ne_true ((hn' (assignment f)).symm.trans (model_formula f full k zero cells h hl hc))

lemma no_model_strong (full : Bool) (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (hn : (strongNat full k zero cells).Unsat) (f : Op) (h : NormalForm f k zero)
    (hl : SecondLex f k zero) (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False := by
  have hn' : (strongFormula full k zero cells).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => number_injective he)).mp (unsat_of_sanitize _ hn)
  exact Bool.false_ne_true ((hn' (assignment f)).symm.trans (model_strongFormula f full k zero cells h hl hc))

end Spectrum.E1483.OrderTwelve.SecondLexEncoding
