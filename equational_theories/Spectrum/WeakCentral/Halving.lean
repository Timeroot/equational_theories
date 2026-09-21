import equational_theories.Spectrum.WeakCentral.Finite
import equational_theories.Spectrum.WeakCentral.Dyadic
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Exact degree halving in finite weak central groupoids

A bad path supplies two disjoint translation fibers inside a return fiber.
This first proves a factor-two degree drop. Minimizing the degree of the bad
endpoint then makes the packing exhaustive, and the degree drop exact.
-/

namespace WeakCentralGroupoid

variable {G : Type*} [WeakCentralGroupoid G]

/-- Rotate an all-good return pentagon. This equivalence needs no finiteness. -/
def returnEquiv (e b : G) :
    {c : G // (e ◇ b) ◇ c = b} ≃ {d : G // d ◇ (e ◇ b) = e} where
  toFun c := ⟨c.1 ◇ e, by
    have h := eqn e c.1 (e ◇ b)
    simpa only [c.2] using h⟩
  invFun d := ⟨b ◇ d.1, by
    have h := dual_eqn b d.1 (e ◇ b)
    simpa only [d.2] using h⟩
  left_inv c := by
    apply Subtype.ext
    have h := dual_eqn c.1 e b
    simpa only [c.2] using h
  right_inv d := by
    apply Subtype.ext
    have h := eqn d.1 b e
    simpa only [d.2] using h

/-- The two old fibers of a bad path pack disjointly into its return fiber. -/
def badPathEmbedding {e a b : G} (hea : Edge e a) (hab : Edge a b)
    (hbad : e ◇ b ≠ a) :
    ({c : G // a ◇ c = b} ⊕ {d : G // d ◇ a = e}) ↪
      {c : G // (e ◇ b) ◇ c = b} where
  toFun
    | .inl c => ⟨c.1, by
        obtain ⟨z, hz⟩ := edge_iff_col.mp hea
        change z ◇ a = e at hz
        calc
          (e ◇ b) ◇ c.1 = ((z ◇ a) ◇ (a ◇ c.1)) ◇ c.1 := by rw [hz, c.2]
          _ = b := (absorption_right z a c.1).trans c.2⟩
    | .inr d => (returnEquiv e b).symm ⟨d.1, by
        obtain ⟨w, hw⟩ := hab
        change a ◇ w = b at hw
        calc
          d.1 ◇ (e ◇ b) = d.1 ◇ ((d.1 ◇ a) ◇ (a ◇ w)) := by rw [d.2, hw]
          _ = e := (absorption d.1 a w).trans d.2⟩
  inj' := by
    intro x y hxy
    cases x with
    | inl c =>
      cases y with
      | inl c' =>
        have hc : c.1 = c'.1 :=
          congrArg (fun z : {c : G // (e ◇ b) ◇ c = b} => z.1) hxy
        exact congrArg Sum.inl (Subtype.ext hc)
      | inr d =>
        exfalso
        have hc : c.1 = b ◇ d.1 := congrArg Subtype.val hxy
        have h := eqn a d.1 b
        rw [← hc, d.2, c.2] at h
        exact hbad h
    | inr d =>
      cases y with
      | inl c =>
        exfalso
        have hc : b ◇ d.1 = c.1 := congrArg Subtype.val hxy
        have h := eqn a d.1 b
        rw [hc, d.2, c.2] at h
        exact hbad h
      | inr d' =>
        apply congrArg Sum.inr
        apply Subtype.ext
        have h := congrArg (fun c => (returnEquiv e b c).1) hxy
        simpa only [Equiv.apply_symm_apply] using h

/-- Any bad two-step path has a middle at least twice the replacement degree. -/
theorem bad_path_degree_double_le [Finite G] {e a b : G}
    (hea : Edge e a) (hab : Edge a b) (hbad : e ◇ b ≠ a) :
    2 * degree (e ◇ b) ≤ degree a := by
  letI : Nonempty G := ⟨a⟩
  have hn : 0 < Nat.card G := Nat.card_pos
  have hA := fiber_card_left hab
  have hB := fiber_card_right hea
  have hT := fiber_card_left (edge_mul_right e b)
  have hAB : Nat.card {c : G // a ◇ c = b} = Nat.card {d : G // d ◇ a = e} := by
    exact Nat.eq_of_mul_eq_mul_left (degree_pos a) (hA.trans hB.symm)
  have hpack := Nat.card_le_card_of_injective _ (badPathEmbedding hea hab hbad).injective
  rw [Nat.card_sum, ← hAB] at hpack
  have hscaled := Nat.mul_le_mul_left (degree (e ◇ b)) hpack
  have hpos : 0 < Nat.card {c : G // a ◇ c = b} := by nlinarith
  nlinarith

/-- For each nonsharp edge, a minimum-degree bad endpoint makes the packing exact. -/
theorem exists_degree_half [Finite G] {e a : G} (hea : Edge e a)
    (hsharp : ¬ Sharp e a) : ∃ b : G, Edge a b ∧ e ◇ b ≠ a ∧
      degree a = 2 * degree (e ◇ b) := by
  classical
  have hex : ({b : G | Edge a b ∧ e ◇ b ≠ a} : Set G).Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, e ◇ (a ◇ x) ≠ a := by simpa only [Sharp, not_forall] using hsharp
    exact ⟨a ◇ x, edge_mul_left a x, hx⟩
  obtain ⟨b, ⟨hab, hbad⟩, hmin⟩ :=
    Set.exists_min_image _ degree (Set.toFinite _) hex
  refine ⟨b, hab, hbad, ?_⟩
  let E := badPathEmbedding hea hab hbad
  -- An uncovered return would give a lower-degree bad endpoint for the same edge.
  have hsurj : Function.Surjective E := by
    intro c
    by_cases hc : a ◇ c.1 = b
    · exact ⟨Sum.inl ⟨c.1, hc⟩, Subtype.ext rfl⟩
    · have hd : (c.1 ◇ e) ◇ a = e := by
        by_contra hd
        have hbad' : e ◇ (a ◇ c.1) ≠ a := by
          intro h
          have hw := eqn e c.1 a
          rw [h] at hw
          exact hd hw
        have hbc : Edge b c.1 := by
          have h := edge_mul_right (e ◇ b) c.1
          rwa [c.2] at h
        have hdrop := bad_path_degree_double_le hab hbc hc
        have hminimal := hmin (a ◇ c.1) ⟨edge_mul_left a c.1, hbad'⟩
        have hpos := degree_pos b
        omega
      refine ⟨Sum.inr ⟨c.1 ◇ e, hd⟩, Subtype.ext ?_⟩
      change b ◇ (c.1 ◇ e) = c.1
      have h := dual_eqn c.1 e b
      simpa only [c.2] using h
  -- Exhaustive packing, together with equal old fiber sizes, gives exact halving.
  have heq := Nat.card_congr (Equiv.ofBijective E ⟨E.injective, hsurj⟩)
  rw [Nat.card_sum] at heq
  have hA := fiber_card_left hab
  have hB := fiber_card_right hea
  have hT := fiber_card_left (edge_mul_right e b)
  have hAB : Nat.card {c : G // a ◇ c = b} = Nat.card {d : G // d ◇ a = e} :=
    Nat.eq_of_mul_eq_mul_left (degree_pos a) (hA.trans hB.symm)
  change Nat.card {c : G // a ◇ c = b} + Nat.card {d : G // d ◇ a = e} =
    Nat.card {c : G // (e ◇ b) ◇ c = b} at heq
  rw [← hAB] at heq
  letI : Nonempty G := ⟨a⟩
  have hn : 0 < Nat.card G := Nat.card_pos
  have hpos : 0 < Nat.card {c : G // a ◇ c = b} := by nlinarith
  have hscaled := congrArg (fun n => degree (e ◇ b) * n) heq
  nlinarith

/-- A nonminimum degree has an exact half among the occurring degrees. -/
theorem degree_half_of_min_lt [Finite G] (h : G)
    (hmin : ∀ x : G, degree h ≤ degree x) (x : G) (hx : degree h < degree x) :
    ∃ y : G, degree x = 2 * degree y := by
  obtain ⟨s, _, hmax⟩ := Set.exists_max_image (Set.univ : Set G) degree
    (Set.toFinite _) ⟨h, Set.mem_univ h⟩
  have hmax' : ∀ x : G, degree x ≤ degree s := fun x => hmax x (Set.mem_univ x)
  have hn := min_max_card h s hmin hmax'
  let e := h ◇ x
  have he : degree e = degree s := by
    have he₁ := edge_card_le (edge_mul_left h x)
    have he₂ := hmax' e
    have hp := degree_pos h
    change Nat.card G ≤ degree h * degree e at he₁
    nlinarith
  have hnonsharp : ¬ Sharp e x := by
    intro hs
    have hcard := sharp_card hs
    rw [he] at hcard
    have hp := degree_pos s
    nlinarith
  obtain ⟨b, _, _, hb⟩ := exists_degree_half (edge_mul_right h x) hnonsharp
  exact ⟨e ◇ b, hb⟩

/-- Every translation degree is dyadic over the minimum degree. -/
theorem degree_eq_min_mul_pow_two [Finite G] (h : G)
    (hmin : ∀ x : G, degree h ≤ degree x) (a : G) :
    ∃ k : ℕ, degree a = degree h * 2 ^ k :=
  eq_min_mul_pow_two degree (degree h) (degree_pos h) hmin
    (degree_half_of_min_lt h hmin) a

/-- There are no gaps between the minimum and maximum dyadic degrees. -/
theorem degree_support [Finite G] (h s : G)
    (hmin : ∀ x : G, degree h ≤ degree x) (hmax : ∀ x : G, degree x ≤ degree s)
    {m : ℕ} (hm : degree s = degree h * 2 ^ m) (D : ℕ) :
    (∃ a : G, degree a = D) ↔ ∃ k ≤ m, D = degree h * 2 ^ k := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := degree_eq_min_mul_pow_two h hmin a
    refine ⟨k, ?_, hk⟩
    have hle := hmax a
    rw [hk, hm] at hle
    have hp := degree_pos h
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by nlinarith)
  · rintro ⟨k, hkm, rfl⟩
    exact exists_eq_min_mul_pow_two degree (degree h) (degree_pos h)
      (degree_half_of_min_lt h hmin) s hm hkm

/-- An edge's row-column rectangle has cardinality equal to the order times a
power of two. In particular, the order divides the product of endpoint degrees. -/
theorem edge_degree_product [Finite G] {e a : G} (hea : Edge e a) :
    ∃ k : ℕ, degree e * degree a = Nat.card G * 2 ^ k := by
  letI : Nonempty G := ⟨a⟩
  obtain ⟨h, _, hmin⟩ := Set.exists_min_image (Set.univ : Set G) degree
    (Set.toFinite _) Set.univ_nonempty
  obtain ⟨s, _, hmax⟩ := Set.exists_max_image (Set.univ : Set G) degree
    (Set.toFinite _) Set.univ_nonempty
  have hmin' : ∀ x : G, degree h ≤ degree x := fun x => hmin x (Set.mem_univ x)
  have hmax' : ∀ x : G, degree x ≤ degree s := fun x => hmax x (Set.mem_univ x)
  obtain ⟨p, hp⟩ := degree_eq_min_mul_pow_two h hmin' e
  obtain ⟨q, hq⟩ := degree_eq_min_mul_pow_two h hmin' a
  obtain ⟨m, hm⟩ := degree_eq_min_mul_pow_two h hmin' s
  have hproduct : degree e * degree a = degree h ^ 2 * 2 ^ (p + q) := by
    rw [hp, hq, pow_add]
    ring
  have hcard : Nat.card G = degree h ^ 2 * 2 ^ m := by
    rw [← min_max_card h s hmin' hmax', hm]
    ring
  have hle : m ≤ p + q := by
    have hbound := edge_card_le hea
    rw [hproduct, hcard] at hbound
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (Nat.le_of_mul_le_mul_left hbound (Nat.pow_pos (degree_pos h)))
  refine ⟨p + q - m, ?_⟩
  rw [hproduct, hcard, mul_assoc, ← pow_add, Nat.add_sub_of_le hle]

/-- The finite order is a square times a power of two, without a full-core hypothesis. -/
theorem card_eq_square_mul_two_pow [Finite G] [Nonempty G] :
    ∃ r m : ℕ, 0 < r ∧ Nat.card G = r ^ 2 * 2 ^ m := by
  obtain ⟨h, _, hmin⟩ := Set.exists_min_image (Set.univ : Set G) degree
    (Set.toFinite _) Set.univ_nonempty
  obtain ⟨s, _, hmax⟩ := Set.exists_max_image (Set.univ : Set G) degree
    (Set.toFinite _) Set.univ_nonempty
  have hmin' : ∀ x : G, degree h ≤ degree x := fun x => hmin x (Set.mem_univ x)
  have hmax' : ∀ x : G, degree x ≤ degree s := fun x => hmax x (Set.mem_univ x)
  obtain ⟨m, hm⟩ := degree_eq_min_mul_pow_two h hmin' s
  refine ⟨degree h, m, degree_pos h, ?_⟩
  rw [← min_max_card h s hmin' hmax', hm]
  ring

/-- info: 'WeakCentralGroupoid.card_eq_square_mul_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_eq_square_mul_two_pow

/-- info: 'WeakCentralGroupoid.degree_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms degree_support

/-- info: 'WeakCentralGroupoid.edge_degree_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edge_degree_product

end WeakCentralGroupoid
