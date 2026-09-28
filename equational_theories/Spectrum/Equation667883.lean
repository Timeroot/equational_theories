import equational_theories.Spectrum.Equation63.IdempotentSeeds
import equational_theories.Spectrum.QuasigroupBounds

/-! Constructive bounds for E667 and E883. Idempotent E63 models transfer
to both laws. Additional companion-matrix constructions give all squares
for E667 and all fourth powers for E883. -/
namespace Spectrum
open Law Law.MagmaLaw

theorem E63.Model.hasModel667 {n : ℕ} (h : E63.Model (Fin n) true) :
    Law667.HasModel n := by
  obtain ⟨op, hl, hi⟩ := h
  refine ⟨⟨op⟩, (@Law667.models_iff _ ⟨op⟩).mpr ?_⟩
  intro x y
  change x = op y (op x (op (op x x) y))
  rw [hi rfl]
  exact (hl x y).symm

/-- The term `q(x,y)=p(x,p(x,y))` turns an idempotent E63 model into E883.
The calculation does not require finiteness. -/
theorem E63.Model.hasModel883 {n : ℕ} (h : E63.Model (Fin n) true) :
    Law883.HasModel n := by
  obtain ⟨op, hl, hi⟩ := h
  let q := fun x y => op x (op x y)
  have hq (x y) : op y (q x y) = x := hl x y
  have qi (y) : q y y = y := by simp [q, hi rfl]
  refine ⟨⟨q⟩, (@Law883.models_iff _ ⟨q⟩).mpr ?_⟩
  intro x y
  change x = q y (q (q x y) (q y y))
  rw [qi]
  change x = op y (op y (q (q x y) y))
  rw [hq, hq]

namespace E667

theorem non_three {n : ℕ} (hn : 0 < n) (hm : n % 3 ≠ 0) : Law667.HasModel n := by
  by_cases he : n = 7
  · subst n; exact E63.idem7.hasModel667
  · apply (loops_667 (a := n) ?_).2
    refine ⟨hn, ?_, by simpa using he⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

def squareOp {R : Type*} [CommRing R] (x y : R × R) : R × R :=
  (-x.2-y.2, x.1+y.1)

theorem square_law {R : Type*} [CommRing R] :
    @Equation667 (R × R) ⟨squareOp⟩ := by
  intro x y
  apply Prod.ext <;> simp only [Magma.op, squareOp] <;> ring

theorem square_model (n : ℕ) [NeZero n] : Law667.HasModel (n^2) := by
  exact hasModel_of_card (⟨squareOp⟩ : Magma (ZMod n × ZMod n))
    ((@Law667.models_iff _ ⟨squareOp⟩).mpr square_law) (by simp [pow_two])

theorem cube_model (n : ℕ) [NeZero n] : Law667.HasModel (n^3) :=
  (E63.cubic_idempotent n).hasModel667

spectrum_assert square_model complete
spectrum_assert cube_model complete

end E667

namespace E883

theorem non_three {n : ℕ} (hn : 0 < n) (hm : n % 3 ≠ 0) : Law883.HasModel n := by
  by_cases he : n = 7
  · subst n; exact E63.idem7.hasModel883
  · apply (loops_883 (a := n) ?_).2
    refine ⟨hn, ?_, by simpa using he⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

def fourthOp {R : Type*} [CommRing R] (x y : R × R × R × R) : R × R × R × R :=
  (-x.2.2.2-y.1+y.2.2.1,
   x.1-y.1-y.2.1+y.2.2.2,
   x.2.1-x.2.2.2-y.1-y.2.1,
   x.2.2.1-x.2.2.2-y.2.1)

theorem fourth_law {R : Type*} [CommRing R] :
    @Equation883 (R × R × R × R) ⟨fourthOp⟩ := by
  intro x y
  apply Prod.ext
  · simp only [Magma.op, fourthOp]; ring
  · apply Prod.ext
    · simp only [Magma.op, fourthOp]; ring
    · apply Prod.ext <;> simp only [Magma.op, fourthOp] <;> ring

theorem fourth_model (n : ℕ) [NeZero n] : Law883.HasModel (n^4) := by
  exact hasModel_of_card (⟨fourthOp⟩ : Magma (ZMod n × ZMod n × ZMod n × ZMod n))
    ((@Law883.models_iff _ ⟨fourthOp⟩).mpr fourth_law)
    (by simp [pow_succ, Nat.mul_assoc])

theorem cube_model (n : ℕ) [NeZero n] : Law883.HasModel (n^3) :=
  (E63.cubic_idempotent n).hasModel883

spectrum_assert fourth_model complete
spectrum_assert cube_model complete

end E883
end Spectrum
