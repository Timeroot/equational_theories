import equational_theories.Spectrum.Equation1483.OrderTwelve.HeadLexNormalization
import equational_theories.Spectrum.Equation1483.OrderTwelve.RowOneEncoding

/-! Prefix flags encode lexicographic minimality under transpositions of the
normalized image. Their meaning is equality of the preceding first-row entries. -/
namespace Spectrum.E1483.OrderTwelve.HeadLexEncoding
open Std.Sat Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalization RowOneNormalization HeadLexNormalization
abbrev A := Fin 12
abbrev Var := Atom 12 ⊕ (A × A × A)
def old (x : Atom 12) : Var := .inl x
def flag (a b i : A) : Var := .inr (a,b,i)
def number : Var → Nat
  | .inl x => code x
  | .inr (a,b,i) => 20736+(a.val*12+b.val)*12+i.val

def assignment (f : A → A → A) : Var → Bool
  | .inl x => meaning f x
  | .inr (a,b,i) => decide (∀ j : A, j < i → f 0 j = swapRow f a b j)

def predClause : CNF Var := ⟨#[[(old (p 0 0 0),false),(old (p 0 1 0),true)]]⟩

def steps (bnd : Nat) (a b i v w : A) : CNF Var :=
  (if v > Equiv.swap a b w then
    ⟨#[[(flag a b i,false),(old (p 0 i v),false),(old (p 0 (Equiv.swap a b i) w),false)]]⟩
  else .empty) ++
  (if v = Equiv.swap a b w ∧ i.val < bnd then
    ⟨#[[(flag a b i,false),(old (p 0 i v),false),(old (p 0 (Equiv.swap a b i) w),false),
      (flag a b (i+1),true)]]⟩
  else .empty)

def extras (k : Nat) (zero : Bool) : CNF Var :=
  all1 fun a => all1 fun b =>
  if 2 ≤ a.val ∧ a < b ∧ b.val ≤ bound k zero then
    ⟨#[[(flag a b 0,true)]]⟩ ++
    all1 (fun i => if i.val ≤ bound k zero then
      all1 (fun v => if v.val ≤ bound k zero then
        all1 (fun w => if w.val ≤ bound k zero then steps (bound k zero) a b i v w
          else .empty) else .empty) else .empty)
  else .empty

def formula (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Var :=
  (RowOneEncoding.formula k zero cells).relabel old ++ predClause ++ extras k zero

def toNat (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Nat :=
  sanitize ((formula k zero cells).relabel number)

lemma number_injective : Function.Injective number := by
  rintro (x|⟨a,b,i⟩) (y|⟨c,d,j⟩) he
  · exact congrArg Sum.inl (code12_injective he)
  · have ht := x.1.isLt
    have hx := x.2.1.isLt
    have hy := x.2.2.1.isLt
    have hz := x.2.2.2.isLt
    simp only [number,code] at he
    omega
  · have ht := y.1.isLt
    have hx := y.2.1.isLt
    have hy := y.2.2.1.isLt
    have hz := y.2.2.2.isLt
    simp only [number,code] at he
    omega
  · simp only [number] at he
    have hi : i = j := Fin.ext (by omega)
    have hb : b = d := Fin.ext (by omega)
    have ha : a = c := Fin.ext (by omega)
    subst c; subst d; subst j
    rfl

lemma model_steps (f : A → A → A) (k : Nat) (zero : Bool)
    (hk : k < 12) (hl : HeadLex f k zero)
    (a b i v w : A) (ha : 2 ≤ a.val) (hab : a < b)
    (hb : b.val ≤ bound k zero) (hi : i.val ≤ bound k zero) :
    CNF.Sat (assignment f) (steps (bound k zero) a b i v w) := by
  apply sat_append
  · split
    next hgt =>
      apply sat_single
      by_cases hp : ∀ j : A, j < i → f 0 j = swapRow f a b j
      swap
      · simp [CNF.Clause.eval,assignment,flag,hp]
      by_cases hv : f 0 i = v
      swap
      · simp [CNF.Clause.eval,assignment,old,meaning,p,hv]
      by_cases hw : f 0 (Equiv.swap a b i) = w
      swap
      · simp [CNF.Clause.eval,assignment,old,meaning,p,hw]
      have hh := hl a b i ha hab hb hi hp
      simp only [swapRow,hv,hw] at hh
      exact (not_lt_of_ge hh hgt).elim
    next => exact CNF.sat_empty
  · split
    next he =>
      apply sat_single
      by_cases hp : ∀ j : A, j < i → f 0 j = swapRow f a b j
      swap
      · simp [CNF.Clause.eval,assignment,flag,hp]
      by_cases hv : f 0 i = v
      swap
      · simp [CNF.Clause.eval,assignment,old,meaning,p,hv]
      by_cases hw : f 0 (Equiv.swap a b i) = w
      swap
      · simp [CNF.Clause.eval,assignment,old,meaning,p,hw]
      have hbnd : bound k zero < 12 := by cases zero <;> simp [bound] <;> omega
      have hnext : (i+1).val = i.val+1 := Fin.val_add_one_of_lt (by change i.val < 11; omega)
      have hp' : ∀ j : A, j < i+1 → f 0 j = swapRow f a b j := by
        intro j hj
        have hjv : j.val < i.val+1 := by change j.val < (i+1).val at hj; omega
        by_cases hji : j < i
        · exact hp j hji
        have hej : j = i := Fin.ext (by change ¬ j.val < i.val at hji; omega)
        subst j
        simpa only [swapRow,hv,hw] using he.1
      simp [CNF.Clause.eval,assignment,flag,old,meaning,p,hv,hw]
      exact Or.inr hp'
    next => exact CNF.sat_empty

lemma model_extras (f : A → A → A) (k : Nat) (zero : Bool)
    (hk : k < 12) (hl : HeadLex f k zero) : CNF.Sat (assignment f) (extras k zero) := by
  apply sat_all1; intro a
  apply sat_all1; intro b
  split
  next h =>
    apply sat_append
    · apply sat_single
      simp [CNF.Clause.eval,assignment,flag]
    · apply sat_all1; intro i
      split
      next hi =>
        apply sat_all1; intro v
        split
        next =>
          apply sat_all1; intro w
          split
          next => exact model_steps f k zero hk hl a b i v w h.1 h.2.1 h.2.2 hi
          next => exact CNF.sat_empty
        next => exact CNF.sat_empty
      next => exact CNF.sat_empty
  next => exact CNF.sat_empty

lemma model_formula (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (f : A → A → A) (hk : k < 12) (h : RankCore f k zero) (hs : Sorted f k zero)
    (ht : (f 0 1).val ≤ 2) (hm : FirstMention f k zero)
    (hI : f 0 0 = 0 → f 0 1 = 0) (hl : HeadLex f k zero)
    (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : CNF.Sat (assignment f) (formula k zero cells) := by
  have hr : CNF.Sat (meaning f) (RowOneEncoding.formula k zero cells) :=
    sat_append _ _ _
      (sat_append _ _ _
        (sat_append _ _ _ (ImageEncoding.model_formula f k zero h hs) (ImageEncoding.model_firstTwo f ht))
        (Encoding.model_units f cells hc)) (RowOneEncoding.model_extras f k zero hm)
  show CNF.Sat (assignment f) (formula k zero cells)
  apply sat_append
  · apply sat_append
    · exact CNF.sat_relabel (by simpa [Function.comp_def,assignment,old] using hr)
    · apply sat_single
      by_cases hh : f 0 0 = 0
      · simp [CNF.Clause.eval,assignment,old,meaning,p,hI hh]
      · simp [CNF.Clause.eval,assignment,old,meaning,p,hh]
  · exact model_extras f k zero hk hl

lemma no_model (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (hn : (toNat k zero cells).Unsat)
    (f : A → A → A) (hk : k < 12) (h : RankCore f k zero) (hs : Sorted f k zero)
    (ht : (f 0 1).val ≤ 2) (hm : FirstMention f k zero)
    (hI : f 0 0 = 0 → f 0 1 = 0) (hl : HeadLex f k zero)
    (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False := by
  have hn' : (formula k zero cells).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => number_injective he)).mp (unsat_of_sanitize _ hn)
  have hh := model_formula k zero cells f hk h hs ht hm hI hl hc
  exact Bool.false_ne_true ((hn' (assignment f)).symm.trans hh)

end Spectrum.E1483.OrderTwelve.HeadLexEncoding
