import equational_theories.Spectrum.Equation1483.PermutationSubalgebra
import equational_theories.Spectrum.WeakCentral.Halving

/-! Permutations do not enlarge subalgebra spectra. A finite subalgebra of an
E1483 permutation cover has an equally large subalgebra in the direct product
of its base and the natural central groupoid on the same fiber size. -/
namespace Spectrum.E1483.PermutationCover
variable {G K S : Type*}

/-- The cover with all coefficient permutations removed. -/
def plain (f : G → G → G) (X Y : G × S × S) : G × S × S :=
  (f X.1 Y.1, X.2.2, Y.2.1)

/-- Replace every coordinate set by the initial segment of the same size. -/
def Shadow (H : Set (G × S × S)) : Set (G × Fin (Nat.card S) × Fin (Nat.card S)) :=
  {X | (∃ u v, (X.1, u, v) ∈ H) ∧
    X.2.1.val < Nat.card (LeftFiber H X.1) ∧ X.2.2.val < Nat.card (RightFiber H X.1)}

private theorem left_size_bound [Finite S] (H : Set (G × S × S)) (x : G) :
    Nat.card (LeftFiber H x) ≤ Nat.card S :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

private theorem right_size_bound [Finite S] (H : Set (G × S × S)) (x : G) :
    Nat.card (RightFiber H x) ≤ Nat.card S :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

private def shadowEquiv [Finite S] (H : Set (G × S × S)) :
    Shadow H ≃ ((x : Base H) ×
      (Fin (Nat.card (LeftFiber H x.val)) × Fin (Nat.card (RightFiber H x.val)))) where
  toFun X := ⟨⟨X.val.1, X.property.1⟩,
    ⟨⟨X.val.2.1.val, X.property.2.1⟩, ⟨X.val.2.2.val, X.property.2.2⟩⟩⟩
  invFun X := ⟨(X.1.val,
    ⟨X.2.1.val, X.2.1.isLt.trans_le (left_size_bound H X.1.val)⟩,
    ⟨X.2.2.val, X.2.2.isLt.trans_le (right_size_bound H X.1.val)⟩),
    X.1.property, X.2.1.isLt, X.2.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equality of the coordinate sizes makes the shadow closed under plain multiplication. -/
theorem shadow_closed [Finite S] {f : G → G → G} {a b : G → G → K}
    {p : K → S ≃ S} {H : Set (G × S × S)} (hH : Closed f a b p H)
    (hf : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    ∀ X ∈ Shadow H, ∀ Y ∈ Shadow H, plain f X Y ∈ Shadow H := by
  intro X hX Y hY
  let x : Base H := ⟨X.1, hX.1⟩
  let y : Base H := ⟨Y.1, hY.1⟩
  have hs := fiber_sizes hH hf x y
  refine ⟨(baseMagma hH).op x y |>.property, ?_, ?_⟩
  · change X.2.2.val < Nat.card (LeftFiber H (f x.val y.val))
    rw [hs.1]
    exact hX.2.2
  · change Y.2.1.val < Nat.card (RightFiber H (f x.val y.val))
    rw [hs.2]
    exact hY.2.1

/-- The shadow has exactly the original subalgebra's cardinality. -/
theorem shadow_card [Finite G] [Finite S] {f : G → G → G} {a b : G → G → K}
    {p : K → S ≃ S} {H : Set (G × S × S)} (hH : Closed f a b p H)
    (h : ∀ X Y Z, extension f a b p (extension f a b p Y X)
      (extension f a b p X (extension f a b p Y Z)) = X) :
    Nat.card (Shadow H) = Nat.card H := by
  classical
  letI := Fintype.ofFinite (Base H)
  rw [Nat.card_congr (shadowEquiv H), Nat.card_congr (subalgebraEquiv h hH)]
  simp only [Nat.card_sigma, Nat.card_prod, Nat.card_fin]

/-- No choice of permutations creates a subalgebra order unavailable in the
plain direct-product cover, on a fiber set of exactly the same size. -/
theorem exists_plain_subalgebra [Finite G] [Finite S]
    {f : G → G → G} {a b : G → G → K} {p : K → S ≃ S}
    {H : Set (G × S × S)} (hH : Closed f a b p H)
    (hf : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (h : ∀ X Y Z, extension f a b p (extension f a b p Y X)
      (extension f a b p X (extension f a b p Y Z)) = X) :
    ∃ T : Set (G × Fin (Nat.card S) × Fin (Nat.card S)),
      (∀ X ∈ T, ∀ Y ∈ T, plain f X Y ∈ T) ∧ Nat.card T = Nat.card H :=
  ⟨Shadow H, shadow_closed hH hf, shadow_card hH h⟩

/-- If the base also satisfies E1485, no permutation cover or subalgebra of it
can leave the square/twice-square spectrum. The shadow supplies an E1485 model
of the same size, without asserting that the original operation satisfies E1485. -/
theorem subalgebra_card_of_1485_base [Finite G] [Finite S]
    {f : G → G → G} {a b : G → G → K} {p : K → S ≃ S}
    {H : Set (G × S × S)} (hH : Closed f a b p H) (hn : H.Nonempty)
    (hf : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (h : ∀ X Y Z, extension f a b p (extension f a b p Y X)
      (extension f a b p X (extension f a b p Y Z)) = X)
    (hw : ∀ x y z, f (f y x) (f x (f z y)) = x) :
    ∃ r : ℕ, Nat.card H = r ^ 2 ∨ Nat.card H = 2 * r ^ 2 := by
  letI : Nonempty H := hn.to_subtype
  have hc := shadow_card hH h
  have hp : 0 < Nat.card (Shadow H) := hc.symm ▸ Nat.card_pos (α := H)
  letI : Nonempty (Shadow H) := (Nat.card_pos_iff.mp hp).1
  letI : WeakCentralGroupoid (Shadow H) :=
    { op := fun X Y => ⟨plain f X.val Y.val, shadow_closed hH hf _ X.property _ Y.property⟩
      eqn := by
        intro X Y Z
        apply Subtype.ext
        exact Prod.ext (hw X.val.1 Y.val.1 Z.val.1) rfl }
  obtain ⟨r, k, _, hk⟩ := WeakCentralGroupoid.card_eq_square_mul_two_pow (G := Shadow H)
  rw [hc] at hk
  exact WeakCentralGroupoid.square_or_twice_square_of_dyadic hk

/-- info: 'Spectrum.E1483.PermutationCover.subalgebra_card_of_1485_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms subalgebra_card_of_1485_base

/-- info: 'Spectrum.E1483.PermutationCover.exists_plain_subalgebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_plain_subalgebra
end Spectrum.E1483.PermutationCover
