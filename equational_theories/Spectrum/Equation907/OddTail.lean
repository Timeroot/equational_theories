import equational_theories.Spectrum.PBD.WilsonPrimePowers
import equational_theories.Spectrum.OpenWitnesses
import equational_theories.Spectrum.Shapes

/-! Every sufficiently large odd order admits an idempotent E907 magma.
Only the block sizes 3 and 23 are needed. Their design periods 6 and 506
have gcd 2; the singleton completes the odd residue class. -/
namespace Spectrum.E907
open Law Law.MagmaLaw

def binaryLaw : PBD.BinaryLaw :=
  let x := FreeMagma.Leaf false
  let y := FreeMagma.Leaf true
  ⟨x, y ⋆ ((y ⋆ x) ⋆ (x ⋆ y))⟩

/-- An unconditional design tail in the odd residue class. -/
theorem odd_design_tail :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → PBD.HasPBD {3,23} n := by
  let K : Finset ℕ := {3,23}
  let C := PBD.designClosure (K : Set ℕ)
  have hC : PBD.DesignClosed C := PBD.designClosure_closed _
  have h3 : 3 ∈ C := PBD.subset_designClosure _ (by simp [K])
  have h23 : 23 ∈ C := PBD.subset_designClosure _ (by simp [K])
  have h1 : 1 ∈ C := PBD.one_mem_designClosure _
  have p3 : PBD.EventuallyPeriodic C 6 := by
    simpa using hC.eventual_period_primePower (p := 3) (e := 1)
      (by decide) (by decide) (by simpa using h3)
  have p23 : PBD.EventuallyPeriodic C 506 := by
    simpa using hC.eventual_period_primePower (p := 23) (e := 1)
      (by decide) (by decide) (by simpa using h23)
  have p2 : PBD.EventuallyPeriodic C 2 := by simpa using p3.gcd p23
  have hU : PBD.UniformOneTail 3 := by
    simpa using PBD.uniform_one_tail_primePower (p := 3) (e := 1)
      (by decide) (by decide)
  have hF := hC.complete_fibres_of_period (by decide) h3 hU (by decide : 0 < 2) p2
  obtain ⟨N,hN⟩ := hF.finite_seeds {1} (by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    subst s
    exact ⟨by decide,h1⟩)
  refine ⟨N,fun n hn ho => PBD.designClosure_finset.mp (hN n hn ?_)⟩
  refine ⟨1,by simp,?_⟩
  change n % 2 = 1 % 2
  obtain ⟨k,hk⟩ := ho
  omega

private def seed3 : PBD.Model binaryLaw (ZMod 3) where
  op := OpenWitnesses.idempotentScalar 2
  idem := OpenWitnesses.idempotentScalar_self 2
  law := by decide

private def seed23 : PBD.Model binaryLaw (ZMod 23) where
  op := OpenWitnesses.idempotentScalar 3
  idem := OpenWitnesses.idempotentScalar_self 3
  law := OpenWitnesses.law907_23

/-- The tail can be realized entirely by idempotent models. -/
theorem eventually_odd_idempotent :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
      Nonempty (PBD.Model binaryLaw (Fin n)) := by
  obtain ⟨N,hN⟩ := odd_design_tail
  refine ⟨N,fun n hn ho => (hN n hn ho).model ?_⟩
  intro k hk
  simp only [Finset.mem_insert,Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact ⟨seed3.transport (Fintype.equivFinOfCardEq (by simp))⟩
  · exact ⟨seed23.transport (Fintype.equivFinOfCardEq (by simp))⟩

/-- All sufficiently large odd orders belong to the E907 spectrum. -/
theorem eventually_odd :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → Law907.HasModel n := by
  obtain ⟨N,hN⟩ := eventually_odd_idempotent
  refine ⟨N,fun n hn ho => ?_⟩
  obtain ⟨M⟩ := hN n hn ho
  exact ⟨⟨M.op⟩, (@Law907.models_iff _ ⟨M.op⟩).mpr M.law⟩

spectrum_assert eventually_odd_idempotent complete
spectrum_assert eventually_odd complete

/-- info: 'Spectrum.E907.eventually_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eventually_odd
end Spectrum.E907
