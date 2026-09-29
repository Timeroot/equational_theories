import equational_theories.Spectrum.Equation1083_1286.DesignWitnesses
import equational_theories.Spectrum.PBD.ResidueFilling
import equational_theories.Spectrum.PBD.Existence
import equational_theories.Spectrum.Shapes

/-! The complete reduction of E1083/E1286 cofiniteness to Wilson's theorem
for block sizes {7,9,16}. No pending declaration is imported here. -/
namespace Spectrum.E1083E1286
open Law Law.MagmaLaw
variable {which : Bool}

private theorem model_of_hasModel {n : ℕ} (h : (law which).HasModel n) :
    Model which (Fin n) := by
  obtain ⟨M,hM⟩ := h
  refine ⟨M.op, ?_, by simp⟩
  cases which
  · exact fun x y => ((@Law1083.models_iff _ M).mp hM x y).symm
  · exact fun x y => ((@Law1286.models_iff _ M).mp hM x y).symm

/-- A tail in just residues zero and one suffices; the tail's models need
not be idempotent. -/
theorem cofinite_of_residue_tail
    (h : ∃ C : ℕ, ∀ n : ℕ, C ≤ n → (n % 3 = 0 ∨ n % 3 = 1) →
      (law which).HasModel n) : CofiniteSpectrum (law which) := by
  obtain ⟨C,hC⟩ := h
  let N := max 1 (max C (PBD.ResidueFilling.cutoff 1008 11 4 C))
  refine ⟨N, fun n hn => ⟨by dsimp [N] at hn; omega, ?_⟩⟩
  by_cases hr : n % 3 = 0 ∨ n % 3 = 1
  · exact hC n (by dsimp [N] at hn; omega) hr
  have hnp : n ≡ 11 [MOD 3] := by change n % 3 = 11 % 3; omega
  obtain ⟨q,t,hq,ht,_,hqp,htp,hgt,hsum,hD⟩ := PBD.ResidueFilling.decompose
    (p := 3) (k := 1008) (g := 11) (e := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (show PBD.ResidueFilling.cutoff 1008 11 4 C ≤ n from by dsimp [N] at hn; omega) hnp
  have mq := model_of_hasModel (hC q hq (Or.inr hqp))
  have mt := model_of_hasModel (hC t ht (Or.inr htp))
  have mr : Model which (Fin (11*t)) :=
    (seed11.product mt).relabel (Fintype.equivFinOfCardEq (by simp))
  rw [← hsum]
  exact hasTD_models hD hgt mq mr idem1008 idem1009

private def binaryLaw (which : Bool) : PBD.BinaryLaw :=
  let x := FreeMagma.Leaf false
  let y := FreeMagma.Leaf true
  if which then ⟨x, y ⋆ (((x ⋆ y) ⋆ x) ⋆ y)⟩
  else ⟨x, y ⋆ ((x ⋆ (y ⋆ x)) ⋆ y)⟩

private theorem to_pbd {A : Type*} (h : Model which A true) :
    Nonempty (PBD.Model (binaryLaw which) A) := by
  obtain ⟨op,hl,hi⟩ := h
  refine ⟨{ op := op, idem := hi rfl, law := ?_ }⟩
  cases which <;> exact fun x y => (hl x y).symm

private theorem from_pbd {A : Type*} (h : PBD.Model (binaryLaw which) A) :
    Model which A true := by
  refine ⟨h.op, ?_, fun _ => h.idem⟩
  cases which <;> exact fun x y => (h.law x y).symm

theorem model_of_pbd {n : ℕ} (h : PBD.HasPBD {7,9,16} n) : Model which (Fin n) true := by
  have seeds : ∀ k ∈ ({7,9,16} : Finset ℕ), Nonempty (PBD.Model (binaryLaw which) (Fin k)) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact to_pbd idem7
    · exact to_pbd idem9
    · exact to_pbd (quartic 2)
  obtain ⟨M⟩ := h.model seeds
  exact from_pbd M

/-- Only the design-existence conclusion for one three-element block set is
needed from Wilson, shared by both laws. -/
theorem cofinite_of_design_tail (h : PBD.ResidueTail {7,9,16} 3) :
    CofiniteSpectrum (law which) := by
  obtain ⟨C,hC⟩ := h
  apply cofinite_of_residue_tail
  exact ⟨C, fun n hn hr => (model_of_pbd (which := which) (hC n hn hr)).hasModel⟩

theorem cofinite_of_wilson (h : PBD.WilsonExistence {7,9,16}) :
    CofiniteSpectrum (law which) := cofinite_of_design_tail h.tail_7_9_16

spectrum_assert cofinite_of_residue_tail complete
spectrum_assert cofinite_of_design_tail complete
spectrum_assert cofinite_of_wilson complete

/-- info: 'Spectrum.E1083E1286.cofinite_of_wilson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cofinite_of_wilson

end Spectrum.E1083E1286
