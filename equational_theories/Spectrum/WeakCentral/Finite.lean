import equational_theories.Spectrum.WeakCentral.Basic
import Mathlib.Data.Finite.Prod

/-!
# Translation degrees of finite weak central groupoids

Sharp edges provide rectangular coordinates. These coordinates show that
translations have uniform fibers, that row and column degrees agree, and that
the least and greatest degrees multiply to the order of the magma.
-/

namespace WeakCentralGroupoid

variable {G : Type*} [original : WeakCentralGroupoid G]

/-- The number of values of a left translation. -/
noncomputable def degree (a : G) : ℕ := Nat.card (Set.range (a ◇ ·))

/-- An ordinary edge in the associated directed graph. -/
def Edge (e a : G) : Prop := a ∈ Set.range (e ◇ ·)

theorem edge_iff_col {e a : G} : Edge e a ↔ e ∈ Set.range (· ◇ a) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(t ◇ e) ◇ e, dual_eqn e t e⟩
  · rintro ⟨t, rfl⟩
    exact ⟨a ◇ (a ◇ t), eqn a t a⟩

theorem edge_mul_left (a b : G) : Edge a (a ◇ b) := ⟨b, rfl⟩

theorem edge_mul_right (a b : G) : Edge (a ◇ b) b :=
  edge_iff_col.mpr ⟨a, rfl⟩

theorem sharp_edge {e a : G} (h : Sharp e a) : Edge e a := ⟨a ◇ e, h e⟩

theorem absorption_right (x y z : G) : ((x ◇ y) ◇ (y ◇ z)) ◇ z = y ◇ z := by
  let opposite : WeakCentralGroupoid G :=
    { op := fun x y => y ◇ x, eqn := fun x y z => dual_eqn x y z }
  exact @absorption G opposite z y x

theorem degree_pos [Finite G] (a : G) : 0 < degree a := by
  letI : Nonempty (Set.range (a ◇ ·)) := ⟨⟨a ◇ a, a, rfl⟩⟩
  exact Nat.card_pos

/-- In sharp rectangular coordinates, a left fiber is the second factor. -/
noncomputable def leftFiberEquiv {e a b : G} (h : Sharp e a) (hb : Edge a b) :
    {x : G // a ◇ x = b} ≃ Set.range (· ◇ e) where
  toFun x := ⟨x.1 ◇ e, x.1, rfl⟩
  invFun v := ⟨b ◇ v.1, by
    exact congrArg (fun p => p.1.1)
      ((sharpProductEquiv h).apply_symm_apply (⟨b, hb⟩, v))⟩
  left_inv x := by
    apply Subtype.ext
    have hx := (sharpProductEquiv h).symm_apply_apply x.1
    change (a ◇ x.1) ◇ (x.1 ◇ e) = x.1 at hx
    simpa only [x.2] using hx
  right_inv v := by
    apply Subtype.ext
    exact congrArg (fun p => p.2.1)
      ((sharpProductEquiv h).apply_symm_apply (⟨b, hb⟩, v))

/-- All nonempty left-translation fibers have the same cardinality. -/
theorem fiber_card_left [Finite G] {a b : G} (hb : Edge a b) :
    degree a * Nat.card {x : G // a ◇ x = b} = Nat.card G := by
  obtain ⟨e, he⟩ := sharp_predecessor a
  rw [Nat.card_congr (leftFiberEquiv he hb)]
  exact ((Nat.card_congr (sharpProductEquiv he)).trans (Nat.card_prod _ _)).symm

theorem sharp_left_fiber {e a : G} (h : Sharp e a) :
    {x : G | e ◇ x = a} = Set.range (a ◇ ·) := by
  ext x
  constructor
  · intro hx
    have he := edge_mul_right e x
    change e ◇ x = a at hx
    rw [hx] at he
    exact he
  · rintro ⟨y, rfl⟩
    exact h y

/-- Left and right translations at the same point have equal ranks. -/
theorem degree_eq_col_card [Finite G] (e : G) :
    degree e = Nat.card (Set.range (· ◇ e)) := by
  obtain ⟨a, ha⟩ := sharp_successor e
  have hf := fiber_card_left (sharp_edge ha)
  have hset := sharp_left_fiber ha
  change degree e * Nat.card {x : G // x ∈ {x : G | e ◇ x = a}} = Nat.card G at hf
  rw [hset] at hf
  change degree e * degree a = Nat.card G at hf
  have hr := (Nat.card_congr (sharpProductEquiv ha)).trans (Nat.card_prod _ _)
  change Nat.card G = degree a * Nat.card (Set.range (· ◇ e)) at hr
  have heq : degree a * degree e = degree a * Nat.card (Set.range (· ◇ e)) := by
    rw [Nat.mul_comm]
    exact hf.trans hr
  exact Nat.eq_of_mul_eq_mul_left (degree_pos a) heq

/-- All nonempty right-translation fibers have the same cardinality. -/
theorem fiber_card_right [Finite G] {a b : G} (hb : Edge b a) :
    degree a * Nat.card {x : G // x ◇ a = b} = Nat.card G := by
  obtain ⟨u, hu⟩ := sharp_successor a
  have hb' := edge_iff_col.mp hb
  let E : {x : G // x ◇ a = b} ≃ Set.range (u ◇ ·) :=
    { toFun := fun x => ⟨u ◇ x.1, x.1, rfl⟩
      invFun := fun v => ⟨v.1 ◇ b, congrArg (fun p => p.2.1)
        ((sharpProductEquiv hu).apply_symm_apply (v, ⟨b, hb'⟩))⟩
      left_inv := fun x => Subtype.ext (by
        have hx := (sharpProductEquiv hu).symm_apply_apply x.1
        change (u ◇ x.1) ◇ (x.1 ◇ a) = x.1 at hx
        simpa only [x.2] using hx)
      right_inv := fun v => Subtype.ext (congrArg (fun p => p.1.1)
        ((sharpProductEquiv hu).apply_symm_apply (v, ⟨b, hb'⟩))) }
  rw [Nat.card_congr E]
  have hc := (Nat.card_congr (sharpProductEquiv hu)).trans (Nat.card_prod _ _)
  rw [← degree_eq_col_card a] at hc
  simpa only [degree, Nat.mul_comm] using hc.symm

/-- Every ordinary edge gives an injection into its row-column rectangle. -/
theorem edge_card_le [Finite G] {e a : G} (h : Edge e a) :
    Nat.card G ≤ degree e * degree a := by
  let f : G → Set.range (a ◇ ·) × Set.range (· ◇ e) :=
    fun x => (⟨a ◇ x, x, rfl⟩, ⟨x ◇ e, x, rfl⟩)
  have hi : Function.Injective f := by
    obtain ⟨t, rfl⟩ := h
    intro x y hxy
    have hh := congrArg (fun p : Set.range ((e ◇ t) ◇ ·) × Set.range (· ◇ e) =>
      p.1.1 ◇ p.2.1) hxy
    exact (dual_eqn x e t).symm.trans (hh.trans (dual_eqn y e t))
  have hc := Nat.card_le_card_of_injective f hi
  rw [Nat.card_prod, ← degree_eq_col_card e] at hc
  simpa only [degree, Nat.mul_comm] using hc

/-- Sharp edges are exact cardinality factorizations. -/
theorem sharp_card [Finite G] {e a : G} (h : Sharp e a) :
    degree e * degree a = Nat.card G := by
  have hc := (Nat.card_congr (sharpProductEquiv h)).trans (Nat.card_prod _ _)
  rw [← degree_eq_col_card e] at hc
  simpa only [degree, Nat.mul_comm] using hc.symm

/-- The minimum and maximum translation degrees multiply to the order. -/
theorem min_max_card [Finite G] (h s : G)
    (hmin : ∀ x : G, degree h ≤ degree x) (hmax : ∀ x : G, degree x ≤ degree s) :
    degree h * degree s = Nat.card G := by
  obtain ⟨a, ha⟩ := sharp_successor h
  obtain ⟨b, hb⟩ := sharp_successor s
  have h₁ := sharp_card ha
  have h₂ := sharp_card hb
  have h₃ := Nat.mul_le_mul_left (degree h) (hmax a)
  have h₄ := Nat.mul_le_mul_left (degree s) (hmin b)
  rw [Nat.mul_comm (degree s) (degree h)] at h₄
  omega

end WeakCentralGroupoid
