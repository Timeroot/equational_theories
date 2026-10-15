import equational_theories.Spectrum.Equation1483.OrderTwelve.Normalization

/-! The CNF for sorting both translation images. In the column image, the
row-zero outputs are strictly increasing: translation regularity makes them
injective there. Outside that image, the outputs are nondecreasing. -/
namespace Spectrum.E1483.OrderTwelve.ImageEncoding
open Std.Sat Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalization
abbrev A := Fin 12

def sortedImages (k : Nat) (zero : Bool) : CNF (Atom 12) := all1 fun y =>
  if bound k zero < y.val ∧ y.val < 11 then
    ⟨#[[(col 0 y,true),(col 0 (y+1),false)]]⟩ ++
    (all1 fun z => all1 fun w =>
      (if z.val ≤ k ∧ w.val ≤ k ∧ w < z then
        ⟨#[[(col 0 y,true),(col 0 (y+1),true),
            (p 0 y z,false),(p 0 (y+1) w,false)]]⟩ else .empty) ++
      (if z.val ≤ k ∧ w.val ≤ k ∧ w ≤ z then
        ⟨#[[(col 0 y,false),(col 0 (y+1),false),
            (p 0 y z,false),(p 0 (y+1) w,false)]]⟩ else .empty))
  else .empty

def coreFormula (k : Nat) (zero : Bool) : CNF (Atom 12) :=
  Magma.Central1483.CNF.formula 12 ++ exactImages ++ regularImages ++ nonfullImages ++
  minimumImages k ++ normalizedImage k zero ++ cardUpper (col 0) k ++ firstCell zero ++
  (if k=3 then rankThreeExtras else .empty) ++ thresholdExtras

def formula (k : Nat) (zero : Bool) : CNF (Atom 12) :=
  coreFormula k zero ++ Encoding.transpose ++ Encoding.paths ++ sortedImages k zero

def toNat (k : Nat) (zero : Bool) : CNF Nat := sanitize ((formula k zero).relabel code)

lemma model_core (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) : CNF.Sat (meaning f) (coreFormula k zero) := by
  have hc : CNF.Sat (meaning f) (cardUpper (col 0) k) := by
    apply sat_cardUpper _ _ _ (colSet f 0) (meaning_col f 0)
    rw [h.cardEq,h.rankZero]
  have ht : CNF.Sat (meaning f) (if k=3 then rankThreeExtras else .empty) := by
    split
    · exact model_rankThreeExtras f k zero h
    · exact CNF.sat_empty
  simp only [coreFormula, CNF.Sat, CNF.eval_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨Magma.Central1483.CNF.model_formula f h.source h.dual,
    model_exactImages f⟩, model_regularImages f h.leftRegular h.rightRegular⟩,
    model_nonfullImages f k zero h⟩, model_minimumImages f k zero h⟩,
    model_normalizedImage f k zero h⟩, hc⟩, model_firstCell f k zero h⟩, ht⟩,
    model_thresholdExtras f k zero h⟩

lemma column_injective (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (i j : A)
    (hi : ∃ x, f x 0 = i) (hj : ∃ x, f x 0 = j) (he : f 0 i = f 0 j) : i = j := by
  obtain ⟨x,rfl⟩ := hi
  obtain ⟨y,rfl⟩ := hj
  calc
    f x 0 = f (f 0 (f x 0)) 0 := (h.rightRegular 0 x).symm
    _ = f (f 0 (f y 0)) 0 := by rw [he]
    _ = f y 0 := h.rightRegular 0 y

lemma sorted_facts (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hs : Sorted f k zero) (i : A)
    (hi : bound k zero < i.val ∧ i.val < 11) :
    ((∃ x, f x 0 = i+1) → ∃ x, f x 0 = i) ∧
    ((¬ ∃ x, f x 0 = i) → (¬ ∃ x, f x 0 = i+1) → f 0 i ≤ f 0 (i+1)) ∧
    ((∃ x, f x 0 = i) → (∃ x, f x 0 = i+1) → f 0 i < f 0 (i+1)) := by
  have hv : (i+1).val = i.val+1 := by
    simp [Fin.val_add,Nat.mod_eq_of_lt (show i.val+1 < 12 by omega)]
  have hij : i < i+1 := by change i.val < (i+1).val; omega
  have hk := hs i (i+1) hi.1 (by omega) hij.le
  have hb := (f 0 (i+1)).isLt
  refine ⟨?_,?_,?_⟩
  · intro hj
    by_contra hn
    simp only [key,hn,hj,↓reduceIte] at hk
    omega
  · intro hi' hj'
    simp only [key,hi',hj',↓reduceIte] at hk
    change (f 0 i).val ≤ (f 0 (i+1)).val
    omega
  · intro hi' hj'
    simp only [key,hi',hj',↓reduceIte] at hk
    have hn : f 0 i ≠ f 0 (i+1) := fun he =>
      (ne_of_lt hij) (column_injective f k zero h i (i+1) hi' hj' he)
    exact lt_of_le_of_ne hk hn

lemma model_sorted (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hs : Sorted f k zero) :
    CNF.Sat (meaning f) (sortedImages k zero) := by
  apply sat_all1
  intro y
  split
  next hy =>
    obtain ⟨hc,hn,hi⟩ := sorted_facts f k zero h hs y hy
    apply sat_append
    · apply sat_single
      by_cases hc' : ∃ x, f x 0 = y+1 <;> simp_all [CNF.Clause.eval,meaning,col]
    · apply sat_all1
      intro z
      apply sat_all1
      intro w
      apply sat_append
      · split
        next hz =>
          apply sat_single
          by_cases hyc : ∃ x, f x 0 = y
          · simp [CNF.Clause.eval,meaning,col,hyc]
          by_cases hnc : ∃ x, f x 0 = y+1
          · simp [CNF.Clause.eval,meaning,col,hnc]
          have hh := hn hyc hnc
          have bad : ¬ (f 0 y = z ∧ f 0 (y+1) = w) := by
            rintro ⟨h1,h2⟩
            rw [h1,h2] at hh
            exact (not_lt_of_ge hh) hz.2.2
          by_cases hzv : f 0 y = z <;> by_cases hwv : f 0 (y+1) = w <;>
            simp_all [CNF.Clause.eval,meaning,p,col]
        next => exact CNF.sat_empty
      · split
        next hz =>
          apply sat_single
          by_cases hyc : ∃ x, f x 0 = y
          · by_cases hnc : ∃ x, f x 0 = y+1
            · have hh := hi hyc hnc
              have bad : ¬ (f 0 y = z ∧ f 0 (y+1) = w) := by
                rintro ⟨h1,h2⟩
                rw [h1,h2] at hh
                exact (not_le_of_gt hh) hz.2.2
              by_cases hzv : f 0 y = z <;> by_cases hwv : f 0 (y+1) = w <;>
                simp_all [CNF.Clause.eval,meaning,p,col]
            · simp [CNF.Clause.eval,meaning,col,hnc]
          · simp [CNF.Clause.eval,meaning,col,hyc]
        next => exact CNF.sat_empty
  next => exact CNF.sat_empty

lemma model_formula (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hs : Sorted f k zero) :
    CNF.Sat (meaning f) (formula k zero) :=
  sat_append _ _ _ (sat_append _ _ _ (sat_append _ _ _ (model_core f k zero h)
    (Encoding.model_transpose f h.source)) (Encoding.model_paths f h.source))
    (model_sorted f k zero h hs)

lemma no_model (k : Nat) (zero : Bool) (hn : (toNat k zero).Unsat)
    (f : A → A → A) (h : RankCore f k zero) (hs : Sorted f k zero) : False := by
  have hn' : (formula k zero).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => code12_injective he)).mp (unsat_of_sanitize _ hn)
  have hh := hn' (meaning f)
  rw [model_formula f k zero h hs] at hh
  contradiction

/-- Name the first new row-image value `2`, before sorting the other points. -/
def firstTwo : CNF (Atom 12) := all1 fun z =>
  if 2 < z.val then ⟨#[[(p 0 1 z,false)]]⟩ else .empty

def smallFormula (k : Nat) (zero : Bool) : CNF (Atom 12) := formula k zero ++ firstTwo

def smallNat (k : Nat) (zero : Bool) : CNF Nat :=
  sanitize ((smallFormula k zero).relabel code)

lemma model_firstTwo (f : A → A → A) (ht : (f 0 1).val ≤ 2) :
    CNF.Sat (meaning f) firstTwo := by
  apply sat_all1
  intro z
  split
  next hz =>
    apply sat_single
    have hn : f 0 1 ≠ z := by intro he; rw [he] at ht; omega
    simp [CNF.Clause.eval,meaning,p,hn]
  next => exact CNF.sat_empty

lemma no_small_model (k : Nat) (zero : Bool) (hn : (smallNat k zero).Unsat)
    (f : A → A → A) (h : RankCore f k zero) (hs : Sorted f k zero)
    (ht : (f 0 1).val ≤ 2) : False := by
  have hn' : (smallFormula k zero).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => code12_injective he)).mp (unsat_of_sanitize _ hn)
  have hm := sat_append _ _ _ (model_formula f k zero h hs) (model_firstTwo f ht)
  exact (Bool.false_ne_true) ((hn' (meaning f)).symm.trans hm)

/-- A small explicit case distinction on table entries. -/
def fixedFormula (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF (Atom 12) :=
  smallFormula k zero ++ Encoding.units cells

def fixedNat (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Nat :=
  sanitize ((fixedFormula k zero cells).relabel code)

lemma no_fixed_model (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (hn : (fixedNat k zero cells).Unsat)
    (f : A → A → A) (h : RankCore f k zero) (hs : Sorted f k zero)
    (ht : (f 0 1).val ≤ 2) (hc : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False := by
  have hn' : (fixedFormula k zero cells).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => code12_injective he)).mp (unsat_of_sanitize _ hn)
  have hm := sat_append _ _ _
    (sat_append _ _ _ (model_formula f k zero h hs) (model_firstTwo f ht))
    (Encoding.model_units f cells hc)
  exact (Bool.false_ne_true) ((hn' (meaning f)).symm.trans hm)

end Spectrum.E1483.OrderTwelve.ImageEncoding
