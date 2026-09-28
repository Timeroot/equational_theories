import equational_theories.Spectrum.Equation1483.ConstantUntwist
import equational_theories.Spectrum.WeakCentral.Halving

/-! A finite E1483 magma with a constant row has power-of-two cardinality.
The operation is untwisted into an E1485 operation on the same carrier. -/

namespace Spectrum.E1483.Constant

variable {G : Type*} [original : Magma G]

def untwist (one x y : G) : G := twist one (twist one x) ◇ twist one y

@[implicit_reducible]
def weakCentral (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) : WeakCentralGroupoid G where
  op := untwist one
  eqn x y z := untwist_eqn h zero one hzero x y z

theorem untwist_constant (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) (x : G) : untwist one zero x = one := by
  simp only [untwist, twist_zero h zero one hzero, hzero]

theorem untwist_commutative (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) (x y : G) :
    untwist one x y = untwist one y x := by
  have he : twist one (twist one x ◇ y) = twist one (twist one y ◇ x) :=
    congrArg (twist one) (twisted_commute h zero one hzero x y)
  rw [twist_mul h zero one hzero, twist_mul h zero one hzero] at he
  exact he

/-- A constant row forces the cardinality to be a power of two. -/
theorem card_pow_two [Finite G] (h : Equation1483 G) (zero one : G)
    (hzero : ∀ t : G, zero ◇ t = one) : ∃ k : ℕ, Nat.card G = 2 ^ k := by
  classical
  have hc := untwist_constant h zero one hzero
  let W : WeakCentralGroupoid G := weakCentral h zero one hzero
  letI : Magma G := W.toMagma
  letI : WeakCentralGroupoid G := W
  letI : Nonempty G := ⟨zero⟩
  have hz : WeakCentralGroupoid.degree zero = 1 := by
    have hr : Set.range (fun x : G => zero ◇ x) = {one} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact hc y
      · intro hx
        exact ⟨zero, (hc zero).trans hx.symm⟩
    rw [WeakCentralGroupoid.degree, hr]
    exact Nat.card_unique
  have hmin : ∀ x : G, WeakCentralGroupoid.degree zero ≤ WeakCentralGroupoid.degree x := by
    intro x
    rw [hz]
    exact WeakCentralGroupoid.degree_pos x
  obtain ⟨s, _, hs⟩ := Set.exists_max_image (Set.univ : Set G)
    WeakCentralGroupoid.degree (Set.toFinite _) Set.univ_nonempty
  have hmax := fun x => hs x (Set.mem_univ x)
  obtain ⟨k, hk⟩ := WeakCentralGroupoid.degree_eq_min_mul_pow_two zero hmin s
  refine ⟨k, ?_⟩
  have hn := WeakCentralGroupoid.min_max_card zero s hmin hmax
  simpa only [hz, hk, one_mul] using hn.symm

/-- The same restriction applies if any row is bijective. -/
theorem card_pow_two_of_bijective [Finite G] (h : Equation1483 G) (a : G)
    (ha : Function.Bijective (fun x => a ◇ x)) : ∃ k : ℕ, Nat.card G = 2 ^ k := by
  obtain ⟨zero, one, hzero⟩ := CentralConstant.bijective_row_gives_constant h a ha
  exact card_pow_two h zero one hzero

/-- Exact spectrum of the constant-row subclass, including the singleton. -/
theorem exists_constant_iff {A : Type*} [Finite A] :
    (∃ M : Magma A, @Equation1483 A M ∧
      ∃ zero one : A, ∀ x : A, M.op zero x = one) ↔
      ∃ k : ℕ, Nat.card A = 2 ^ k := by
  constructor
  · rintro ⟨M, hM, zero, one, hzero⟩
    exact @card_pow_two A M _ hM zero one hzero
  · rintro ⟨k, hk⟩
    classical
    letI := Fintype.ofFinite A
    let B := Fin k → Bool
    have hc : Fintype.card A = Fintype.card B := by
      simpa [B, Nat.card_eq_fintype_card] using hk
    let e : A ≃ B := Fintype.equivOfCardEq hc
    let nand : B → B → B := fun x y i => !(x i && y i)
    let M : Magma A := ⟨fun x y => e.symm (nand (e x) (e y))⟩
    refine ⟨M, ?_, e.symm (fun _ => false), e.symm (fun _ => true), ?_⟩
    · intro x y z
      apply e.injective
      change e x = e (e.symm (nand
        (e (e.symm (nand (e y) (e x))))
        (e (e.symm (nand (e x) (e (e.symm (nand (e y) (e z)))))))))
      simp only [Equiv.apply_symm_apply]
      funext i
      change e x i = !(!(e y i && e x i) && !(e x i && !(e y i && e z i)))
      cases e x i <;> cases e y i <;> cases e z i <;> decide
    · intro x
      change e.symm (nand (e (e.symm (fun _ => false))) (e x)) = _
      congr 1
      simp only [Equiv.apply_symm_apply]
      funext i
      simp [nand]

/-- info: 'Spectrum.E1483.Constant.card_pow_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_pow_two

/-- info: 'Spectrum.E1483.Constant.card_pow_two_of_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_pow_two_of_bijective

/-- info: 'Spectrum.E1483.Constant.exists_constant_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_constant_iff

end Spectrum.E1483.Constant
