import equational_theories.Spectrum.PBD.WilsonPrimePowers
import equational_theories.Spectrum.OpenWitnesses
import equational_theories.Spectrum.QuarticSeeds
import equational_theories.Spectrum.Shapes

/-!
# Cofiniteness of E670

The idempotent models of orders 9, 11, and 16 glue over pairwise balanced
designs. The design closure has eventual periods 72, 110, and 240, hence
period 2. Its positive seeds 1 and 16 occupy both parity classes, so the
closure contains every sufficiently large order. All design existence
results used here are proved constructively in the imported PBD modules;
Wilson's general theorem is not assumed.
-/

namespace Spectrum.PBD

/-- Every sufficiently large order has a PBD with block sizes 9, 11, and 16. -/
theorem tail_9_11_16 : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasPBD {9,11,16} n := by
  let K : Finset ℕ := {9,11,16}
  let C := designClosure (K : Set ℕ)
  have hC : DesignClosed C := designClosure_closed _
  have h9 : 9 ∈ C := subset_designClosure _ (by simp [K])
  have h11 : 11 ∈ C := subset_designClosure _ (by simp [K])
  have h16 : 16 ∈ C := subset_designClosure _ (by simp [K])
  have h1 : 1 ∈ C := one_mem_designClosure _
  have p9 : EventuallyPeriodic C 72 := by
    simpa using hC.eventual_period_primePower (p := 3) (e := 2)
      (by decide) (by decide) (by simpa using h9)
  have p11 : EventuallyPeriodic C 110 := by
    simpa using hC.eventual_period_primePower (p := 11) (e := 1)
      (by decide) (by decide) (by simpa using h11)
  have p16 : EventuallyPeriodic C 240 := by
    simpa using hC.eventual_period_primePower (p := 2) (e := 4)
      (by decide) (by decide) (by simpa using h16)
  have p2 : EventuallyPeriodic C 2 := by simpa using (p9.gcd p11).gcd p16
  have hU : UniformOneTail 9 := by
    simpa using uniform_one_tail_primePower (p := 3) (e := 2) (by decide) (by decide)
  have hF := hC.complete_fibres_of_period (by decide) h9 hU (by decide : 0 < 2) p2
  obtain ⟨N,hN⟩ := hF.finite_seeds {1,16} (by
    intro s hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨by decide,h1⟩
    · exact ⟨by decide,h16⟩)
  refine ⟨N,fun n hn => designClosure_finset.mp (hN n hn ?_)⟩
  by_cases h : n % 2 = 0
  · exact ⟨16,by simp,by change n % 2 = 16 % 2; omega⟩
  · exact ⟨1,by simp,by change n % 2 = 1 % 2; omega⟩

/-- The usual Wilson formulation follows from the stronger unrestricted tail. -/
theorem wilson_9_11_16 : WilsonExistence {9,11,16} := by
  obtain ⟨N,hN⟩ := tail_9_11_16
  exact ⟨N,fun n hn _ => hN n hn⟩

end Spectrum.PBD

namespace Spectrum.E670
open Law Law.MagmaLaw

def binaryLaw : PBD.BinaryLaw :=
  let x := FreeMagma.Leaf false
  let y := FreeMagma.Leaf true
  ⟨x, y ⋆ (x ⋆ ((x ⋆ y) ⋆ y))⟩

private def seed9 : PBD.Model binaryLaw (ZMod 3 × ZMod 3) where
  op := OpenWitnesses.op670_9
  idem := OpenWitnesses.op670_9_idempotent
  law := OpenWitnesses.law670_9

private def seed11 : PBD.Model binaryLaw (ZMod 11) where
  op := OpenWitnesses.idempotentScalar 6
  idem := OpenWitnesses.idempotentScalar_self 6
  law := OpenWitnesses.law670_11_idempotent

private def seed16 : PBD.Model binaryLaw (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) where
  op := QuarticSeeds.op (-1) 1 0 (-2)
  idem := QuarticSeeds.idempotent (-1) 1 0 (-2)
  law := QuarticSeeds.law_670

/-- Gluing preserves both the law and idempotence. -/
theorem idempotent_model_of_pbd {n : ℕ} (h : PBD.HasPBD {9,11,16} n) :
    Nonempty (PBD.Model binaryLaw (Fin n)) := by
  have seeds : ∀ k ∈ ({9,11,16} : Finset ℕ), Nonempty (PBD.Model binaryLaw (Fin k)) := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact ⟨seed9.transport (Fintype.equivFinOfCardEq (by simp))⟩
    · exact ⟨seed11.transport (Fintype.equivFinOfCardEq (by simp))⟩
    · exact ⟨seed16.transport (Fintype.equivFinOfCardEq (by simp))⟩
  exact h.model seeds

/-- An E670 model is obtained by gluing the three idempotent seed models. -/
theorem model_of_pbd {n : ℕ} (h : PBD.HasPBD {9,11,16} n) : Law670.HasModel n := by
  obtain ⟨M⟩ := idempotent_model_of_pbd h
  exact ⟨⟨M.op⟩, (@Law670.models_iff _ ⟨M.op⟩).mpr M.law⟩

/-- The constructed cofinite family consists of idempotent models. -/
theorem idempotent_tail :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Nonempty (PBD.Model binaryLaw (Fin n)) := by
  obtain ⟨N,hN⟩ := PBD.tail_9_11_16
  exact ⟨N,fun n hn => idempotent_model_of_pbd (hN n hn)⟩

/-- E670 has models of every sufficiently large finite order. -/
theorem cofinite : CofiniteSpectrum Law670 := by
  obtain ⟨N,hN⟩ := PBD.tail_9_11_16
  exact ⟨max 1 N,fun n hn => ⟨by omega,model_of_pbd (hN n (by omega))⟩⟩

spectrum_assert model_of_pbd complete
spectrum_assert idempotent_tail complete
spectrum_assert cofinite complete

/-- info: 'Spectrum.E670.cofinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cofinite

end Spectrum.E670
