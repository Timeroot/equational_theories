import equational_theories.Spectrum.Equation677.DesignWitnesses
import equational_theories.Spectrum.PBD.ResidueFilling
import equational_theories.Spectrum.PBD.Existence
import equational_theories.Spectrum.Shapes

/-! E677 cofiniteness reduced to Wilson's theorem for {5,11,16}.
All gluing, seed, divisibility and CRT arguments are proved here or imported
from complete modules. Wilson's theorem itself is an explicit hypothesis. -/
namespace Spectrum.E677
open Law Law.MagmaLaw

private theorem model_of_hasModel {n : ℕ} (h : Law677.HasModel n) : Model (Fin n) := by
  obtain ⟨M,hM⟩ := h
  exact ⟨M.op, fun x y => ((@Law677.models_iff _ M).mp hM x y).symm, by simp⟩

private theorem missing_residue {C g n : ℕ}
    (hC : ∀ m : ℕ, C ≤ m → (m % 5 = 0 ∨ m % 5 = 1) → Law677.HasModel m)
    (hg : g.Prime) (hpg : 5 ≠ g) (hgk : g ≤ 80) (hkg : Nat.Coprime 80 g)
    (hpow : 80 ≤ g^4) (hpowp : g^4 ≡ 1 [MOD 5]) (seed : Model (Fin g))
    (hn : PBD.ResidueFilling.cutoff 80 g 4 C ≤ n) (hnp : n ≡ g [MOD 5]) :
    Law677.HasModel n := by
  obtain ⟨q,t,hq,ht,_,hqp,htp,hgt,hsum,hD⟩ := PBD.ResidueFilling.decompose
    (by decide) hg hpg (by decide) hgk hkg (by decide) (by decide) hpow hpowp hn hnp
  have mq := model_of_hasModel (hC q hq (Or.inr hqp))
  have mt := model_of_hasModel (hC t ht (Or.inr htp))
  have mr : Model (Fin (g*t)) := (seed.product mt).relabel (Fintype.equivFinOfCardEq (by simp))
  rw [← hsum]
  exact eighty_groups hD hgt mq mr

theorem cofinite_of_residue_tail
    (h : ∃ C : ℕ, ∀ n : ℕ, C ≤ n → (n % 5 = 0 ∨ n % 5 = 1) → Law677.HasModel n) :
    CofiniteSpectrum Law677 := by
  obtain ⟨C,hC⟩ := h
  let N := max 1 (max C (max (PBD.ResidueFilling.cutoff 80 7 4 C)
    (max (PBD.ResidueFilling.cutoff 80 13 4 C) (PBD.ResidueFilling.cutoff 80 19 4 C))))
  refine ⟨N, fun n hn => ⟨by dsimp [N] at hn; omega, ?_⟩⟩
  by_cases hr : n % 5 = 0 ∨ n % 5 = 1
  · exact hC n (by dsimp [N] at hn; omega) hr
  have cases : n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases cases with h | h | h
  · apply missing_residue hC (g := 7) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) seed7
    · dsimp [N] at hn; omega
    · change n % 5 = 7 % 5; omega
  · apply missing_residue hC (g := 13) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) seed13
    · dsimp [N] at hn; omega
    · change n % 5 = 13 % 5; omega
  · apply missing_residue hC (g := 19) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) seed19
    · dsimp [N] at hn; omega
    · change n % 5 = 19 % 5; omega

private def binaryLaw : PBD.BinaryLaw :=
  let x := FreeMagma.Leaf false
  let y := FreeMagma.Leaf true
  ⟨x, y ⋆ (x ⋆ ((y ⋆ x) ⋆ y))⟩

private theorem to_pbd {A : Type*} (h : Model A true) :
    Nonempty (PBD.Model binaryLaw A) := by
  obtain ⟨op,hl,hi⟩ := h
  exact ⟨{ op := op, idem := hi rfl, law := fun x y => (hl x y).symm }⟩

private theorem from_pbd {A : Type*} (h : PBD.Model binaryLaw A) : Model A true :=
  ⟨h.op, fun x y => (h.law x y).symm, fun _ => h.idem⟩

theorem idem11 : Model (Fin 11) true :=
  scalar_idempotent 10 2 (by decide) (by decide) (by decide)

theorem model_of_pbd {n : ℕ} (h : PBD.HasPBD {5,11,16} n) : Model (Fin n) true := by
  have seeds : ∀ k ∈ ({5,11,16} : Finset ℕ), Nonempty (PBD.Model binaryLaw (Fin k)) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact to_pbd idem5
    · exact to_pbd idem11
    · exact to_pbd (quartic 2)
  obtain ⟨M⟩ := h.model seeds
  exact from_pbd M

theorem cofinite_of_design_tail (h : PBD.ResidueTail {5,11,16} 5) :
    CofiniteSpectrum Law677 := by
  obtain ⟨C,hC⟩ := h
  apply cofinite_of_residue_tail
  exact ⟨C, fun n hn hr => (model_of_pbd (hC n hn hr)).hasModel⟩

theorem cofinite_of_wilson (h : PBD.WilsonExistence {5,11,16}) :
    CofiniteSpectrum Law677 := cofinite_of_design_tail h.tail_5_11_16

spectrum_assert cofinite_of_residue_tail complete
spectrum_assert cofinite_of_design_tail complete
spectrum_assert cofinite_of_wilson complete

/-- info: 'Spectrum.E677.cofinite_of_wilson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cofinite_of_wilson

end Spectrum.E677
