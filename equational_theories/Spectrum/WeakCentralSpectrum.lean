import equational_theories.Spectrum.WeakCentral.Halving
import equational_theories.Spectrum.WeakCentral.Dyadic
import equational_theories.Spectrum.Constructions
import equational_theories.Spectrum.Generated.Two
import equational_theories.Spectrum.Shapes

/-!
# The complete finite spectrum of E1485

Every nonempty finite weak central groupoid has order `r² * 2^m`: its
translation degrees are successive doublings of their minimum. Thus its order
is a square or twice a square. Central groupoids and their products with the
two-element model realize every such order.

`hasModel_1485_iff` includes the empty model; `spectrum_1485` uses the project's
positive-order convention. Neither proof uses enumeration or additional axioms.
-/

namespace Spectrum

/-- E1485 has a finite model exactly at square and twice-square orders. -/
theorem hasModel_1485_iff (n : ℕ) :
    Law1485.HasModel n ↔ ∃ q : ℕ, n = q ^ 2 ∨ n = 2 * q ^ 2 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact ⟨0, Or.inl (by simpa using hn)⟩
    obtain ⟨M, hM⟩ := h
    letI : NeZero n := ⟨hn⟩
    letI : WeakCentralGroupoid (Fin n) :=
      { op := M.op
        eqn := fun x y z => ((@Law1485.models_iff (Fin n) M).mp hM x y z).symm }
    obtain ⟨r, m, _, hcard⟩ :=
      WeakCentralGroupoid.card_eq_square_mul_two_pow (G := Fin n)
    apply WeakCentralGroupoid.square_or_twice_square_of_dyadic (r := r) (k := m)
    simpa using hcard
  · rintro ⟨q, rfl | rfl⟩
    · exact square_1485 q
    · exact two_1485.mul (square_1485 q)

/-- The positive finite spectrum of E1485 is exactly the squares and twice-squares. -/
theorem spectrum_1485 : Law1485.spectrum = squares ∪ twiceSquares := by
  ext n
  simp only [Law.MagmaLaw.mem_spectrum, hasModel_1485_iff, Set.mem_union,
    squares, twiceSquares, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, q, hq | hq⟩
    · exact Or.inl ⟨hn, q, hq⟩
    · exact Or.inr ⟨hn, q, hq⟩
  · rintro (⟨hn, q, hq⟩ | ⟨hn, q, hq⟩)
    · exact ⟨hn, q, Or.inl hq⟩
    · exact ⟨hn, q, Or.inr hq⟩

/-- info: 'Spectrum.hasModel_1485_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasModel_1485_iff

/-- info: 'Spectrum.spectrum_1485' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spectrum_1485

end Spectrum
