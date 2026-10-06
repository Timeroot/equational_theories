import equational_theories.Spectrum.Equation467.OrderSixteen.StrongSymmetry
import equational_theories.Spectrum.Equation467.OrderSixteen.CertificateEncoding
import equational_theories.Spectrum.Equation467.OrderSixteen.Coverage

namespace Spectrum.E467.OrderSixteen.Encoding
open Std.Sat
open E63.OrderTen.Encoding (Atom p meaning all1 sat_all1 sat_single sat_append code)

def rotations (i : Case) : CNF (Atom 16) := all1 fun s =>
  if 0 < s.val ∧ s.val < rootLength i then
    all1 fun a => all1 fun b =>
      if (rootPerm i s b).val < a.val then
        ⟨#[[(p (scanRow i) (rootPosition i) a,false),
          (p ((rootPerm i s).symm (scanRow i))
            ((rootPerm i s).symm (rootPosition i)) b,false)]]⟩
      else .empty
  else .empty

theorem model_rotations (i : Case) (f : Point → Point → Point)
    (hf : InCase i f) (hm : Minimal i f) : (rotations i).Sat (meaning f) := by
  apply sat_all1; intro s
  split
  · apply sat_all1; intro a
    apply sat_all1; intro b
    split
    · rename_i hab
      apply sat_single
      by_cases ha : f (scanRow i) (rootPosition i) = a
      · have hb : f ((rootPerm i s).symm (scanRow i))
            ((rootPerm i s).symm (rootPosition i)) ≠ b := by
          intro hb
          have h := minimal_rotation i f hf hm s
          rw [ha,hb] at h
          exact (not_lt_of_ge h) hab
        simp [CNF.Clause.eval,meaning,p,hb]
      · simp [CNF.Clause.eval,meaning,p,ha]
    · exact CNF.sat_empty
  · exact CNF.sat_empty

def optimizedFormula (rotate : Ref → Bool) (r : Ref) : CNF (Atom 16) :=
  refFormula r ++ if rotate r then rotations (refCase r) else .empty

def natOptimized (rotate : Ref → Bool) (r : Ref) : CNF ℕ :=
  sanitize ((optimizedFormula rotate r).relabel code)

theorem model_optimized (rotate : Ref → Bool) (i : Case) (f : Point → Point → Point)
    (hf : InCase i f) (hm : Minimal i f) :
    (optimizedFormula rotate (selectRef i (f 0 (inverseDiagonal i 0)))).Sat (meaning f) := by
  apply sat_append
  · exact model_ref i f hf hm
  · split
    · rw [(select_checked i (f 0 (inverseDiagonal i 0))).1]
      exact model_rotations i f hf hm
    · exact CNF.sat_empty

theorem impossible_of_optimized (rotate : Ref → Bool) (i : Case) (f : Point → Point → Point)
    (hf : InCase i f) (hm : Minimal i f)
    (hu : ∀ r : Ref, (natOptimized rotate r).Unsat) : False := by
  let r := selectRef i (f 0 (inverseDiagonal i 0))
  have hu' : ((optimizedFormula rotate r).relabel code).Unsat := by
    intro a
    cases he : (((optimizedFormula rotate r).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natOptimized rotate r).Sat a := by
        simp only [CNF.Sat,CNF.eval,natOptimized,sanitize,Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hu r a
      rw [hs] at hh
      exact Bool.noConfusion hh
  have hraw := (CNF.unsat_relabel_iff (fun _ _ he => code16_injective he)).mp hu'
  have hh := hraw (meaning f)
  rw [model_optimized rotate i f hf hm] at hh
  contradiction

end Encoding

theorem exclusion_of_optimized (rotate : Ref → Bool)
    (hu : ∀ r : Ref, (Encoding.natOptimized rotate r).Unsat) : ¬ Law467.HasModel 16 := by
  rintro ⟨M,hM⟩
  let f : Point → Point → Point := @Magma.op _ M
  have hf : Holds f := (@Law467.models_iff _ M).mp hM
  obtain ⟨i,g,hg⟩ := exists_case f hf
  obtain ⟨g,hg,hm⟩ := exists_minimal i g hg
  exact Encoding.impossible_of_optimized rotate i g hg hm hu

spectrum_assert exclusion_of_optimized complete
end Spectrum.E467.OrderSixteen
