import equational_theories.Spectrum.Equation1483.OrderTwelve.HeadLexEncoding
import equational_theories.Spectrum.Equation1483.OrderTwelve.SharpEncoding

/-! Combining image-label symmetry with the sharp identities at saturated
rank bounds. Each group of clauses retains its already proved interpretation. -/
namespace Spectrum.E1483.OrderTwelve.CombinedEncoding
open Std.Sat Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalization RowOneNormalization HeadLexNormalization HeadLexEncoding
abbrev A := Fin 12

def formula (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Var :=
  HeadLexEncoding.formula k zero cells ++
    (SharpEncoding.chain ++ SharpEncoding.sharpExtras k zero).relabel old

def toNat (k : Nat) (zero : Bool) (cells : List Encoding.Cell) : CNF Nat :=
  sanitize ((formula k zero cells).relabel number)

lemma model_formula (f : A → A → A) (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (hk : k < 12) (h : RankCore f k zero) (hs : Sorted f k zero)
    (ht : (f 0 1).val ≤ 2) (hm : FirstMention f k zero)
    (hI : f 0 0 = 0 → f 0 1 = 0) (hl : HeadLex f k zero)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1)
    (hf : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) :
    CNF.Sat (assignment f) (formula k zero cells) := by
  have hr : CNF.Sat (meaning f) (RowOneEncoding.formula k zero cells) :=
    sat_append _ _ _
      (sat_append _ _ _
        (sat_append _ _ _ (ImageEncoding.model_formula f k zero h hs)
          (ImageEncoding.model_firstTwo f ht))
        (Encoding.model_units f cells hf)) (RowOneEncoding.model_extras f k zero hm)
  apply sat_append
  · apply sat_append
    · apply sat_append
      · exact CNF.sat_relabel (by simpa [Function.comp_def,assignment,old] using hr)
      · apply sat_single
        by_cases hh : f 0 0 = 0
        · simp [CNF.Clause.eval,assignment,old,meaning,p,hI hh]
        · simp [CNF.Clause.eval,assignment,old,meaning,p,hh]
    · exact model_extras f k zero hk hl
  · apply CNF.sat_relabel
    simpa [Function.comp_def,assignment,old] using
      (sat_append _ _ _ (SharpEncoding.model_chain f hc)
        (SharpEncoding.model_sharpExtras f k zero h))

lemma no_model (k : Nat) (zero : Bool) (cells : List Encoding.Cell)
    (hn : (toNat k zero cells).Unsat)
    (f : A → A → A) (hk : k < 12) (h : RankCore f k zero) (hs : Sorted f k zero)
    (ht : (f 0 1).val ≤ 2) (hm : FirstMention f k zero)
    (hI : f 0 0 = 0 → f 0 1 = 0) (hl : HeadLex f k zero)
    (hc : ∀ y, (f 0 y).val ≤ y.val + 1)
    (hf : ∀ c ∈ cells, f c.1 c.2.1 = c.2.2) : False := by
  have hn' : (formula k zero cells).Unsat :=
    (CNF.unsat_relabel_iff (fun _ _ he => number_injective he)).mp (unsat_of_sanitize _ hn)
  exact Bool.false_ne_true ((hn' (assignment f)).symm.trans
    (model_formula f k zero cells hk h hs ht hm hI hl hc hf))
end Spectrum.E1483.OrderTwelve.CombinedEncoding
