import equational_theories.Spectrum.Equation1483.OrderTwelve.ImageEncoding
import equational_theories.Spectrum.Equation1483.SharpCoordinates

/-! If the edge rank bound is saturated, rectangular coordinates give sharp
identities. The rank-two and rank-three cases can use these identities unless
the neighbor has rank at least seven or five, respectively. -/
namespace Spectrum.E1483.OrderTwelve.SharpEncoding
open Std.Sat Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalization
abbrev A := Fin 12

def chain : CNF (Atom 12) := all1 fun y => all1 fun z =>
  if 2 ≤ y.val ∧ y.val + 1 < z.val then ⟨#[[(p 0 y z,false)]]⟩ else .empty

def chainFormula (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF (Atom 12) :=
  ImageEncoding.fixedFormula k zero cells ++ chain

def threshold (k : Nat) : Nat := 12 / k + 1

def flag (k : Nat) (b : A) : Atom 12 :=
  if k=2 then (6,b,0,0) else (9,b,0,0)

def sharpExtras (k : Nat) (zero : Bool) : CNF (Atom 12) :=
  if k=2 ∨ k=3 then all1 fun b =>
    if (if zero then b.val < k else 0 < b.val ∧ b.val ≤ k) then
      guard (flag k b,false) (cardLower (row b) (threshold k)) ++
      (all1 fun x => all1 fun u =>
        ⟨#[[(flag k b,true),(p b x u,false),(p 0 u b,true)],
           [(flag k b,true),(p x 0 u,false),(p u b 0,true)]]⟩)
    else .empty
  else .empty

def sharpFormula (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF (Atom 12) :=
  chainFormula k zero cells ++ sharpExtras k zero

def sharpNat (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Nat :=
  sanitize ((sharpFormula k zero cells).relabel code)

lemma meaning_flag (f : A → A → A) (k : Nat) (hk : k=2 ∨ k=3) (b : A) :
    meaning f (flag k b) = decide (threshold k ≤ rowSize f b) := by
  rcases hk with rfl | rfl <;> simp [flag,threshold,meaning]

/-- Saturation follows from the edge lower bound and the guard's upper bound. -/
lemma sharp_of_small (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hk : k=2 ∨ k=3) (b : A)
    (hb : ∃ z, f 0 z = b) (hr : rowSize f b < threshold k) :
    (∀ x, f 0 (f b x) = b) ∧ (∀ x, f (f x 0) b = 0) := by
  have hs : 12 = rowSize f 0 * rowSize f b := by
    obtain ⟨z,hz⟩ := hb
    have hlow := h.rowRank 0 z
    rw [hz,h.rankZero] at hlow
    rw [h.rankZero]
    rcases hk with rfl | rfl <;> simp only [threshold] at hr <;> omega
  letI : Magma A := ⟨f⟩
  have he : Equation1483 A := fun x y z => (h.source x y z).symm
  have hcard (a : A) : Nat.card (RankRigidity.Row a) = rowSize f a :=
    (Ranks.rank_natCard f a).symm
  have hs' : Nat.card A = Nat.card (RankRigidity.Row (0:A)) * Nat.card (RankRigidity.Row b) := by
    rw [hcard,hcard]
    simpa [A,Nat.card_eq_fintype_card] using hs
  exact ⟨SharpCoordinates.sharp_left he hb hs',SharpCoordinates.sharp_right he hb hs'⟩

lemma model_chain (f : A → A → A) (hc : ∀ y, (f 0 y).val ≤ y.val+1) :
    CNF.Sat (meaning f) chain := by
  apply sat_all1; intro y
  apply sat_all1; intro z
  split
  next hz =>
    apply sat_single
    have hn : f 0 y ≠ z := by intro he; have := hc y; rw [he] at this; omega
    simp [CNF.Clause.eval,meaning,p,hn]
  next => exact CNF.sat_empty

lemma model_sharpExtras (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) : CNF.Sat (meaning f) (sharpExtras k zero) := by
  unfold sharpExtras
  split
  next hk =>
    apply sat_all1; intro b
    by_cases hb : (if zero then b.val < k else 0 < b.val ∧ b.val ≤ k)
    · rw [if_pos hb]
      have hedge : ∃ z, f 0 z = b := (h.imageZero b).mpr hb
      apply sat_append
      · apply sat_guard
        by_cases hr : threshold k ≤ rowSize f b
        · right
          exact sat_cardLower _ _ _ (rowSet f b) (meaning_row f b) hr
        · left
          simp [meaning_flag f k hk b,hr]
      · apply sat_all1; intro x
        apply sat_all1; intro u
        by_cases hr : threshold k ≤ rowSize f b
        · have hf : meaning f (flag k b) = true := by rw [meaning_flag f k hk b]; simp [hr]
          apply sat_two <;> simp [CNF.Clause.eval,hf]
        · have hf : meaning f (flag k b) = false := by rw [meaning_flag f k hk b]; simp [hr]
          obtain ⟨hl,hr'⟩ := sharp_of_small f k zero h hk b hedge (by omega)
          apply sat_two
          · by_cases hu : f b x = u
            · have he : f 0 u = b := by simpa [hu] using hl x
              simp [CNF.Clause.eval,hf,show meaning f (p b x u) = true by simp [meaning,p,hu],
                show meaning f (p 0 u b) = true by simp [meaning,p,he]]
            · simp [CNF.Clause.eval,hf,show meaning f (p b x u) = false by simp [meaning,p,hu]]
          · by_cases hu : f x 0 = u
            · have he : f u b = 0 := by simpa [hu] using hr' x
              simp [CNF.Clause.eval,hf,show meaning f (p x 0 u) = true by simp [meaning,p,hu],
                show meaning f (p u b 0) = true by simp [meaning,p,he]]
            · simp [CNF.Clause.eval,hf,show meaning f (p x 0 u) = false by simp [meaning,p,hu]]
    · rw [if_neg hb]
      exact CNF.sat_empty
  next => exact CNF.sat_empty

lemma model_formula (f : A → A → A) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hs : Sorted f k zero)
    (hc : ∀ y, (f 0 y).val ≤ y.val+1) (cells : List Encoding.Cell)
    (hf : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) :
    CNF.Sat (meaning f) (sharpFormula k zero cells) := by
  apply sat_append
  · apply sat_append
    · apply sat_append
      · apply sat_append
        · exact ImageEncoding.model_formula f k zero h hs
        · exact ImageEncoding.model_firstTwo f (by simpa using hc 1)
      · exact Encoding.model_units f cells hf
    · exact model_chain f hc
  · exact model_sharpExtras f k zero h

lemma no_model (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (hn : (sharpNat k zero cells).Unsat)
    (f : A → A → A) (h : RankCore f k zero) (hs : Sorted f k zero)
    (hc : ∀ y, (f 0 y).val ≤ y.val+1) (hf : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False := by
  have hn' : (sharpFormula k zero cells).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => code12_injective he)).mp (unsat_of_sanitize _ hn)
  have hm := model_formula f k zero h hs hc cells hf
  exact (Bool.false_ne_true) ((hn' (meaning f)).symm.trans hm)
end Spectrum.E1483.OrderTwelve.SharpEncoding
