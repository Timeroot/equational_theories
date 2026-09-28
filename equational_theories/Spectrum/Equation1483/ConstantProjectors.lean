import equational_theories.Spectrum.Equation1483.ConstantSpectrum

/-! Mixed translations in the constant-row subclass of E1483 are idempotents
and preserve one another's fixed points. The untwist identifies them with the
mixed translations of the associated E1485 magma. No finiteness is needed. -/
namespace Spectrum.E1483.Constant

variable {G : Type*} [Magma G] (h : Equation1483 G) (zero one : G)
  (hzero : ∀ t : G, zero ◇ t = one)

include h hzero

/-- The cubic twist changes only the two parameters of a mixed translation. -/
theorem mixed_untwist (a b t : G) :
    untwist one (twist one a) (untwist one t (twist one b)) = a ◇ (t ◇ b) := by
  simp only [untwist, twist_mul h zero one hzero, twist_three h zero one hzero]

theorem mixed_idempotent (a b t : G) :
    a ◇ ((a ◇ (t ◇ b)) ◇ b) = a ◇ (t ◇ b) := by
  let W := weakCentral h zero one hzero
  have he := @WeakCentralGroupoid.mixed_idempotent G W (twist one a) (twist one b) t
  change untwist one (twist one a)
      (untwist one (untwist one (twist one a) (untwist one t (twist one b)))
        (twist one b)) =
    untwist one (twist one a) (untwist one t (twist one b)) at he
  simpa only [mixed_untwist h zero one hzero] using he

theorem mixed_preserves_fixed (a b c u : G) (hu : a ◇ (u ◇ b) = u) :
    a ◇ ((a ◇ (u ◇ c)) ◇ b) = a ◇ (u ◇ c) := by
  let W := weakCentral h zero one hzero
  have hbu : untwist one (twist one a) (untwist one u (twist one b)) = u :=
    (mixed_untwist h zero one hzero a b u).trans hu
  have he := @WeakCentralGroupoid.mixed_preserves_fixed G W
    (twist one a) (twist one b) (twist one c) u hbu
  change untwist one (twist one a)
      (untwist one (untwist one (twist one a) (untwist one u (twist one c)))
        (twist one b)) =
    untwist one (twist one a) (untwist one u (twist one c)) at he
  simpa only [mixed_untwist h zero one hzero] using he

/-- info: 'Spectrum.E1483.Constant.mixed_idempotent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mixed_idempotent

/-- info: 'Spectrum.E1483.Constant.mixed_preserves_fixed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mixed_preserves_fixed

end Spectrum.E1483.Constant
