import equational_theories.Equations.All
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Prod

/-! The redundant dual identity used in the finite E1483 target search. -/

namespace CentralDual

theorem dual {G : Type*} [Magma G] (h : Equation1483 G) (x y z : G) :
    ((z ◇ y) ◇ x) ◇ (x ◇ y) = x := by
  calc
    ((z ◇ y) ◇ x) ◇ (x ◇ y) =
        ((z ◇ y) ◇ x) ◇ (x ◇ ((z ◇ y) ◇ (y ◇ (z ◇ y)))) :=
      congrArg (fun t => ((z ◇ y) ◇ x) ◇ (x ◇ t)) (h y z y)
    _ = x := (h x (z ◇ y) (y ◇ (z ◇ y))).symm

theorem left_regular {G : Type*} [Magma G] (h : Equation1483 G) (x y : G) :
    x ◇ ((x ◇ y) ◇ x) = x ◇ y := by
  calc
    x ◇ ((x ◇ y) ◇ x) =
        (((x ◇ y) ◇ x) ◇ (x ◇ y)) ◇ ((x ◇ y) ◇ x) :=
      congrArg (fun t => t ◇ ((x ◇ y) ◇ x)) (dual h x y x).symm
    _ = x ◇ y := dual h (x ◇ y) x (x ◇ y)

theorem right_regular {G : Type*} [Magma G] (h : Equation1483 G) (x y : G) :
    (x ◇ (y ◇ x)) ◇ x = y ◇ x := by
  calc
    (x ◇ (y ◇ x)) ◇ x =
        (x ◇ (y ◇ x)) ◇ ((y ◇ x) ◇ (x ◇ (y ◇ x))) :=
      congrArg (fun t => (x ◇ (y ◇ x)) ◇ t) (h x y x)
    _ = y ◇ x := (h (y ◇ x) x (y ◇ x)).symm

/-- Left and right translations restrict to inverse bijections on their images. -/
def translationImageEquiv {G : Type*} [Magma G] (h : Equation1483 G) (x : G) :
    {z : G // ∃ y, x ◇ y = z} ≃ {z : G // ∃ y, y ◇ x = z} where
  toFun a := ⟨a.val ◇ x, a.val, rfl⟩
  invFun b := ⟨x ◇ b.val, b.val, rfl⟩
  left_inv a := by
    apply Subtype.ext
    obtain ⟨y, hy⟩ := a.property
    change x ◇ (a.val ◇ x) = a.val
    rw [← hy]
    exact left_regular h x y
  right_inv b := by
    apply Subtype.ext
    obtain ⟨y, hy⟩ := b.property
    change (x ◇ b.val) ◇ x = b.val
    rw [← hy]
    exact right_regular h x y

/-- An idempotent's left and right translations jointly distinguish all elements. -/
theorem idempotent_pair_injective {G : Type*} [Magma G] (h : Equation1483 G)
    (a : G) (ha : a ◇ a = a) :
    Function.Injective (fun x : G => (a ◇ x, x ◇ a)) := by
  intro x y hxy
  have hx : x = (a ◇ x) ◇ (x ◇ a) := by simpa only [ha] using h x a a
  have hy : y = (a ◇ y) ◇ (y ◇ a) := by simpa only [ha] using h y a a
  have hl : a ◇ x = a ◇ y := congrArg Prod.fst hxy
  have hr : x ◇ a = y ◇ a := congrArg Prod.snd hxy
  rw [hl, hr] at hx
  exact hx.trans hy.symm

/-- In a finite model, an idempotent's row has at least the square root of the carrier size. -/
theorem idempotent_row_bound {G : Type*} [Magma G] [Finite G] (h : Equation1483 G)
    (a : G) (ha : a ◇ a = a) :
    Nat.card G ≤ (Nat.card {z : G // ∃ y, a ◇ y = z}) ^ 2 := by
  classical
  letI := Fintype.ofFinite G
  let embed : G → {z : G // ∃ y, a ◇ y = z} × {z : G // ∃ y, y ◇ a = z} :=
    fun x => (⟨a ◇ x, x, rfl⟩, ⟨x ◇ a, x, rfl⟩)
  have hinj : Function.Injective embed := by
    intro x y he
    apply idempotent_pair_injective h a ha
    exact congrArg (fun p => (p.1.val, p.2.val)) he
  have hle := Nat.card_le_card_of_injective embed hinj
  rw [Nat.card_prod, ← Nat.card_congr (translationImageEquiv h a)] at hle
  simpa only [pow_two] using hle

theorem idempotent_injective_row {G : Type*} [Magma G] (h : Equation1483 G)
    (a : G) (ha : a ◇ a = a) (hi : Function.Injective (fun x => a ◇ x))
    (x : G) : x = a := by
  have ht := h a a x
  rw [ha] at ht
  have h1 : a = a ◇ (a ◇ x) := hi (ha.trans ht)
  have h2 : a = a ◇ x := hi (ha.trans h1)
  exact (hi (ha.trans h2)).symm

theorem row_edge_pair_injective {G : Type*} [Magma G] (h : Equation1483 G)
    (a z : G) : Function.Injective (fun x : G => (a ◇ x, x ◇ (a ◇ z))) := by
  intro x y hxy
  have hl : a ◇ x = a ◇ y := congrArg Prod.fst hxy
  have hr : x ◇ (a ◇ z) = y ◇ (a ◇ z) := congrArg Prod.snd hxy
  calc
    x = (a ◇ x) ◇ (x ◇ (a ◇ z)) := h x a z
    _ = (a ◇ y) ◇ (y ◇ (a ◇ z)) := by rw [hl, hr]
    _ = y := (h y a z).symm

theorem row_edge_rank_bound {G : Type*} [Magma G] [Finite G] (h : Equation1483 G)
    (a z : G) : Nat.card G ≤
      Nat.card {u : G // ∃ x, a ◇ x = u} *
        Nat.card {v : G // ∃ x, (a ◇ z) ◇ x = v} := by
  classical
  letI := Fintype.ofFinite G
  let embed : G → {u : G // ∃ x, a ◇ x = u} × {v : G // ∃ x, x ◇ (a ◇ z) = v} :=
    fun x => (⟨a ◇ x, x, rfl⟩, ⟨x ◇ (a ◇ z), x, rfl⟩)
  have hinj : Function.Injective embed := by
    intro x y he
    apply row_edge_pair_injective h a z
    exact congrArg (fun p => (p.1.val, p.2.val)) he
  have hle := Nat.card_le_card_of_injective embed hinj
  rw [Nat.card_prod, ← Nat.card_congr (translationImageEquiv h (a ◇ z))] at hle
  exact hle

theorem col_edge_rank_bound {G : Type*} [Magma G] [Finite G] (h : Equation1483 G)
    (a z : G) : Nat.card G ≤
      Nat.card {u : G // ∃ x, a ◇ x = u} *
        Nat.card {v : G // ∃ x, (z ◇ a) ◇ x = v} := by
  classical
  letI := Fintype.ofFinite G
  let embed : G → {u : G // ∃ x, (z ◇ a) ◇ x = u} × {v : G // ∃ x, x ◇ a = v} :=
    fun x => (⟨(z ◇ a) ◇ x, x, rfl⟩, ⟨x ◇ a, x, rfl⟩)
  have hinj : Function.Injective embed := by
    intro x y he
    have hl : (z ◇ a) ◇ x = (z ◇ a) ◇ y := congrArg (fun p => p.1.val) he
    have hr : x ◇ a = y ◇ a := congrArg (fun p => p.2.val) he
    calc
      x = ((z ◇ a) ◇ x) ◇ (x ◇ a) := (dual h x a z).symm
      _ = ((z ◇ a) ◇ y) ◇ (y ◇ a) := by rw [hl, hr]
      _ = y := dual h y a z
  have hle := Nat.card_le_card_of_injective embed hinj
  rw [Nat.card_prod, ← Nat.card_congr (translationImageEquiv h a)] at hle
  simpa only [Nat.mul_comm] using hle

/-- A neighboring right translation is injective on each left-translation fiber. -/
theorem row_edge_fiber_bound {G : Type*} [Magma G] [Finite G] (h : Equation1483 G)
    (a z u : G) : Nat.card {x : G // a ◇ x = u} ≤
      Nat.card {v : G // ∃ x, (a ◇ z) ◇ x = v} := by
  let embed : {x : G // a ◇ x = u} → {v : G // ∃ x, x ◇ (a ◇ z) = v} :=
    fun x => ⟨x.val ◇ (a ◇ z), x.val, rfl⟩
  have hinj : Function.Injective embed := by
    intro x y he
    apply Subtype.ext
    apply row_edge_pair_injective h a z
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact congrArg Subtype.val he
  have hle := Nat.card_le_card_of_injective embed hinj
  rw [← Nat.card_congr (translationImageEquiv h (a ◇ z))] at hle
  exact hle

/-- info: 'CentralDual.dual' does not depend on any axioms -/
#guard_msgs in
#print axioms dual

/-- info: 'CentralDual.left_regular' does not depend on any axioms -/
#guard_msgs in
#print axioms left_regular

/-- info: 'CentralDual.right_regular' does not depend on any axioms -/
#guard_msgs in
#print axioms right_regular

/-- info: 'CentralDual.translationImageEquiv' does not depend on any axioms -/
#guard_msgs in
#print axioms translationImageEquiv

/-- info: 'CentralDual.idempotent_pair_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms idempotent_pair_injective

/-- info: 'CentralDual.idempotent_row_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idempotent_row_bound

/-- info: 'CentralDual.idempotent_injective_row' does not depend on any axioms -/
#guard_msgs in
#print axioms idempotent_injective_row

/-- info: 'CentralDual.row_edge_rank_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms row_edge_rank_bound

/-- info: 'CentralDual.col_edge_rank_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms col_edge_rank_bound

/-- info: 'CentralDual.row_edge_fiber_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms row_edge_fiber_bound

end CentralDual
