import equational_theories.Parastrophes.Equation917SandwichCandidate

/-!
# Row comparisons in E917 compression candidates

These are reductions, not single-equation characterizations. Suppose
`F(x,y)=a(x)`, every row carries b to a, and a candidate supplies a row
index k(x) with `y*(k(x)*(x*y))=x`. Comparing this with the F identity gives
`b(k(x)*z)=q(x)*z`. Apply this equation at b(z) in two ways: cancellation
then forces a and b to commute.

If first-argument shifts a and b induce output shifts f and g, respectively,
the same comparison proves that b commutes with f and f commutes with g.
This replaces a 99-line automated derivation for one of the candidate
identities. It does not assert that the shifts are trivial, or that b and g
commute. Neither the formula for q nor finiteness is needed in this lemma.
-/
namespace Parastrophes.Eq917Image.FramePermutations

variable {A : Type*} (m : A → A → A) (q a b k : A → A)
    (rows : ∀ x, Function.Bijective (m x))
    (cross : ∀ x y, m y (m (q x) (m x y)) = a x)
    (rightShift : ∀ x y, m x (b y) = a (m x y))
    (frame : ∀ x y, m y (m (k x) (m x y)) = x)

include rows cross rightShift frame in
/-- The candidate's new row is a shifted old row. -/
theorem row_comparison (x z : A) : b (m (k x) z) = m (q x) z := by
  obtain ⟨y, rfl⟩ := (rows x).2 z
  apply (rows y).1
  rw [rightShift, frame, cross]

include rows cross rightShift frame in
/-- Every row conjugates b to a; the two rows above therefore force ab=ba. -/
theorem commute_ab : Function.Commute a b := by
  intro t
  obtain ⟨z, hz⟩ := (rows (k t)).2 t
  have h := row_comparison m q a b k rows cross rightShift frame t (b z)
  rw [rightShift, rightShift,
    ← row_comparison m q a b k rows cross rightShift frame t z, hz] at h
  exact h.symm

variable (f g : A → A)
    (leftA : ∀ x y, m (a x) y = f (m x y))
    (leftB : ∀ x y, m (b x) y = g (m x y))

include rows rightShift leftA in
/-- Left and right shifts commute at the output. -/
theorem commute_af : Function.Commute a f := by
  intro t
  obtain ⟨z, hz⟩ := (rows t).2 t
  have h : m (a t) (b z) = m (a t) (b z) := rfl
  conv_lhs at h => rw [leftA, rightShift]
  conv_rhs at h => rw [rightShift, leftA]
  simpa only [hz] using h.symm

include rows rightShift leftB in
/-- The second first-argument shift also commutes with a at the output. -/
theorem commute_ag : Function.Commute a g := by
  intro t
  obtain ⟨z, hz⟩ := (rows t).2 t
  have h : m (b t) (b z) = m (b t) (b z) := rfl
  conv_lhs at h => rw [leftB, rightShift]
  conv_rhs at h => rw [rightShift, leftB]
  simpa only [hz] using h.symm

include rows cross rightShift leftA in
/-- Moving a through the first argument determines the corresponding q-row. -/
theorem q_row_shift (x z : A) : m (q (a x)) (f z) = b (m (q x) z) := by
  obtain ⟨y, rfl⟩ := (rows x).2 z
  apply (rows y).1
  rw [← leftA, cross, rightShift, cross]

include rows cross rightShift frame leftA in
/-- A second row comparison gives fb=bf. -/
theorem commute_fb : Function.Commute f b := by
  intro z
  apply (rows (q (a z))).1
  rw [q_row_shift m q a b rows cross rightShift f leftA,
    rightShift, rightShift,
    q_row_shift m q a b rows cross rightShift f leftA]
  exact (commute_ab m q a b k rows cross rightShift frame _).symm

include rows cross rightShift frame leftA leftB in
/-- The commuting first-argument shifts induce commuting output shifts. -/
theorem commute_fg : Function.Commute f g := by
  intro t
  obtain ⟨z, hz⟩ := (rows t).2 t
  have h := congrArg (fun x => m x z)
    (commute_ab m q a b k rows cross rightShift frame t)
  simpa only [leftA, leftB, hz] using h

end Parastrophes.Eq917Image.FramePermutations
