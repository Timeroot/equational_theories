import equational_theories.Spectrum.Equation1486.SquareRows

/-! A singleton square-row forces every E1486 magma, including an infinite one,
to be trivial. The argument was found by Vampire and reconstructed equationally. -/
namespace Spectrum.E1486.SquareRows

variable {G : Type*} (f : G → G → G) (h : Lawful f)

include h in
/-- Constancy of multiplication by squares at one point forces triviality. -/
theorem eq_of_singleton_row (a b : G) (hs : ∀ z, f a (f z z) = b)
    (x y : G) : x = y := by
  have h3 (u v : G) : f b (f (f u u) (f v v)) = f u u := by
    simpa only [hs] using h (f u u) a v
  have h4 (u v : G) : f (f u b) (f v v) = b := by
    simpa only [h3] using h b u (f v v)
  have h5 (u : G) : f b (f u u) = b := by
    calc
      f b (f u u) = f (f a (f (f b b) (f b b))) (f u u) := by rw [hs]
      _ = f (f a b) (f u u) := by rw [h4 b b]
      _ = b := h4 a u
  have hsquare (u : G) : f u u = b := by
    calc
      f u u = f b (f (f u u) (f u u)) := (h3 u u).symm
      _ = b := h5 (f u u)
  have hba : b = a := by
    have ht := h a a a
    rw [hs, hsquare, hsquare] at ht
    exact ht
  have hsquare' (u : G) : f u u = a := (hsquare u).trans hba
  have hcentral (u v : G) : f (f u v) (f v a) = v := by
    simpa only [hsquare'] using h v u a
  have hright (u : G) : f u a = a := by
    have hr : f (f u a) a = a := by
      simpa only [hsquare'] using hcentral u a
    have ht := hcentral (f u a) (f u a)
    simpa only [hsquare', hr] using ht.symm
  have hall (u : G) : u = a := by
    simpa only [hright] using (hcentral a u).symm
  exact (hall x).trans (hall y).symm

include h in
/-- A nontrivial finite E1486 magma has at least two values in each square-row. -/
theorem two_le_row_card [Fintype G] [DecidableEq G] [Nontrivial G] (a : G) :
    2 ≤ (row f a).card := by
  by_contra hn
  have hc : (row f a).card = 1 := by
    have hp := Finset.card_pos.mpr (row_nonempty f a)
    omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hc
  have hs (z : G) : f a (f z z) = b := by
    have hz : f a (f z z) ∈ row f a := (mem_row f a _).mpr ⟨z, rfl⟩
    simpa only [hb, Finset.mem_singleton] using hz
  obtain ⟨x, y, hxy⟩ := exists_pair_ne G
  exact hxy (eq_of_singleton_row f h a b hs x y)

include h in
/-- Every nontrivial finite E1486 magma has order at least four. -/
theorem four_le_card [Fintype G] [DecidableEq G] [Nontrivial G] :
    4 ≤ Fintype.card G := by
  obtain ⟨a, _, ha⟩ := exists_small_row f h
  have hr := two_le_row_card f h a
  nlinarith

/-- info: 'Spectrum.E1486.SquareRows.eq_of_singleton_row' does not depend on any axioms -/
#guard_msgs in
#print axioms eq_of_singleton_row

end Spectrum.E1486.SquareRows
