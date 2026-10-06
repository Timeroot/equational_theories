import equational_theories.Spectrum.Equation667ConstantDiagonal

/-! A left-division presentation of finite E667, for smaller finite-search
encodings. The original multiplication is recovered by left division again.
If `d = x ◇ x`, the new table satisfies `q (q d (q x y)) x = y` and
`q x d = x`. Thus the intermediate binary table used by the original SAT
encoding can be eliminated. -/
namespace Spectrum.E667.Division
variable {Q : Type*} [Magma Q] [Finite Q]

def op (x y : Q) : Q := y ◇ ((y ◇ y) ◇ x)

omit [Finite Q] in
theorem mul_op (h : Equation667 Q) (x y : Q) : x ◇ op x y = y :=
  (h y x).symm

theorem op_mul (h : Equation667 Q) (x y : Q) : op x (x ◇ y) = y := by
  apply E667883.left_injective667 h x
  exact mul_op h x (x ◇ y)

theorem left_injective (h : Equation667 Q) (x : Q) : Function.Injective (op x) := by
  intro y z he
  simpa only [mul_op h] using congrArg (fun a => x ◇ a) he

theorem right_injective (h : Equation667 Q) (y : Q) :
    Function.Injective (fun x => op x y) := by
  intro x z he
  exact E667883.left_injective667 h (y ◇ y) (E667883.left_injective667 h y he)

theorem square_entry (h : Equation667 Q) (x : Q) : op x (x ◇ x) = x :=
  op_mul h x x

/-- The square of the original multiplication is read from one entry of q. -/
theorem square_iff (h : Equation667 Q) (x d : Q) : op x d = x ↔ d = x ◇ x := by
  constructor
  · intro hd
    exact (left_injective h x) (hd.trans (square_entry h x).symm)
  · rintro rfl
    exact square_entry h x

theorem idempotent_iff (h : Equation667 Q) (x : Q) : op x x = x ↔ x ◇ x = x := by
  rw [square_iff h]
  exact eq_comm

/-- The conditional cubic law used by the division-table encoding. -/
theorem cubic (h : Equation667 Q) (x d y : Q) (hd : op x d = x) :
    op (op d (op x y)) x = y := by
  obtain rfl := (square_iff h x d).mp hd
  change x ◇ ((x ◇ x) ◇ op (x ◇ x) (op x y)) = y
  rw [mul_op h, mul_op h]

/-- A constant diagonal in the new table is a right identity in the old one. -/
theorem constant_diagonal_iff (h : Equation667 Q) (e : Q) :
    (∀ x, op x x = e) ↔ ∀ x, x ◇ e = x := by
  constructor
  · intro he x
    rw [← he x, mul_op h]
  · intro he x
    apply E667883.left_injective667 h x
    exact (mul_op h x x).trans (he x).symm

theorem right_identity_iff (h : Equation667 Q) (e : Q) :
    (∀ x, op x e = x) ↔ ∀ x, x ◇ x = e := by
  simp only [square_iff h, eq_comm]

spectrum_assert cubic complete
spectrum_assert square_iff complete
spectrum_assert constant_diagonal_iff complete
spectrum_assert right_identity_iff complete
end Spectrum.E667.Division
