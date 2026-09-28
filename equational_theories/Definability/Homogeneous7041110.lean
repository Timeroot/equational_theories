import equational_theories.Definability.Homogeneous1516.Normalization

/-! Elementary restrictions on homogeneous finite-field targets of E704 and
E1110. These are restrictions on equivariant interpretations, not exclusions
of arbitrary models of the same cardinality. -/

namespace Definability.Homogeneous7041110

open GLTwo1516 Homogeneous1516

variable {K : Type} [Field K] [Finite K] {p : K → K → K}

omit [Finite K] in
lemma zero_column (hp : Homogeneous p) (h2 : (2 : K) ≠ 0) (x : K) :
    p x 0 = x * p 1 0 := by
  by_cases hx : x = 0
  · simp [hx, zero_zero hp h2]
  · simpa using hp x 1 0 hx

omit [Finite K] in
theorem zero_constraint_704 (hp : Homogeneous p) (h2 : (2 : K) ≠ 0)
    (h : ∀ x y, x = p y (p y (p (p x x) y))) :
    (p 0 1)^2 * p 1 1 * p 1 0 = 1 := by
  have he := h 1 0
  rw [zero_row hp h2 (p 0 (p (p 1 1) 0)),
    zero_row hp h2 (p (p 1 1) 0), zero_column hp h2 (p 1 1)] at he
  calc
    _ = p 0 1 * (p 0 1 * (p 1 1 * p 1 0)) := by ring
    _ = 1 := he.symm

omit [Finite K] in
theorem zero_constraint_1110 (hp : Homogeneous p) (h2 : (2 : K) ≠ 0)
    (h : ∀ x y, x = p y (p (p y (p x x)) y)) :
    (p 0 1)^2 * p 1 1 * p 1 0 = 1 := by
  have he := h 1 0
  rw [zero_row hp h2 (p (p 0 (p 1 1)) 0),
    zero_column hp h2 (p 0 (p 1 1)), zero_row hp h2 (p 1 1)] at he
  calc
    _ = p 0 1 * (p 0 1 * p 1 1 * p 1 0) := by ring
    _ = 1 := he.symm

omit [Field K] in
lemma left_injective_704
    (h : ∀ x y, x = p y (p y (p (p x x) y))) (a : K) :
    Function.Injective (p a) := by
  apply (Finite.injective_iff_surjective).mpr
  intro x
  exact ⟨p a (p (p x x) a), (h x a).symm⟩

lemma right_injective_704
    (h : ∀ x y, x = p y (p y (p (p x x) y))) (a : K) :
    Function.Injective (fun x => p x a) := by
  have hd : Function.Injective (fun x => p x x) := by
    intro x y he
    change p x x = p y y at he
    calc
      x = p 0 (p 0 (p (p x x) 0)) := h x 0
      _ = p 0 (p 0 (p (p y y) 0)) := by rw [he]
      _ = y := (h y 0).symm
  intro x y he
  obtain ⟨u, rfl⟩ := Finite.surjective_of_injective hd x
  obtain ⟨v, rfl⟩ := Finite.surjective_of_injective hd y
  change p (p u u) a = p (p v v) a at he
  have huv : u = v := by
    calc
      u = p a (p a (p (p u u) a)) := h u a
      _ = p a (p a (p (p v v) a)) := by rw [he]
      _ = v := (h v a).symm
  rw [huv]

omit [Field K] in
lemma left_injective_1110
    (h : ∀ x y, x = p y (p (p y (p x x)) y)) (a : K) :
    Function.Injective (p a) := by
  apply (Finite.injective_iff_surjective).mpr
  intro x
  exact ⟨p (p a (p x x)) a, (h x a).symm⟩

lemma right_injective_1110
    (h : ∀ x y, x = p y (p (p y (p x x)) y)) (a : K) :
    Function.Injective (fun x => p x a) := by
  have hd : Function.Injective (fun x => p a (p x x)) := by
    intro x y he
    change p a (p x x) = p a (p y y) at he
    calc
      x = p a (p (p a (p x x)) a) := h x a
      _ = p a (p (p a (p y y)) a) := by rw [he]
      _ = y := (h y a).symm
  intro x y he
  obtain ⟨u, rfl⟩ := Finite.surjective_of_injective hd x
  obtain ⟨v, rfl⟩ := Finite.surjective_of_injective hd y
  change p (p a (p u u)) a = p (p a (p v v)) a at he
  have huv : u = v := by
    calc
      u = p a (p (p a (p u u)) a) := h u a
      _ = p a (p (p a (p v v)) a) := by rw [he]
      _ = v := (h v a).symm
  rw [huv]

/-- A homogeneous finite E704 target cannot have squaring map `x ↦ -x`. -/
theorem square_ne_neg_one_704 (hp : Homogeneous p) (h2 : (2 : K) ≠ 0)
    (h : ∀ x y, x = p y (p y (p (p x x) y))) : p 1 1 ≠ -1 := by
  intro hs
  have hm : p (-1) (-1) = 1 := by
    rw [diagonal hp h2, hs]; ring
  have he := h (-1) 1
  rw [hm, hs] at he
  have hf : p 1 (-1) = 1 := left_injective_704 h 1 (he.symm.trans hs.symm)
  have hn : p (-1) 1 = -1 := by
    have hh := hp (-1) 1 (-1) (neg_ne_zero.mpr one_ne_zero)
    simpa [hf] using hh
  have hh : (-1 : K) = 1 := right_injective_704 h 1 (hn.trans hs.symm)
  exact h2 (by linear_combination -hh)

/-- A homogeneous finite E1110 target cannot have squaring map `x ↦ -x`. -/
theorem square_ne_neg_one_1110 (hp : Homogeneous p) (h2 : (2 : K) ≠ 0)
    (h : ∀ x y, x = p y (p (p y (p x x)) y)) : p 1 1 ≠ -1 := by
  intro hs
  have hm : p (-1) (-1) = 1 := by
    rw [diagonal hp h2, hs]; ring
  have he := h (-1) 1
  rw [hm, hs] at he
  have hf : p (-1) 1 = 1 := left_injective_1110 h 1 (he.symm.trans hs.symm)
  have hn : p 1 (-1) = -1 := by
    have hh := hp (-1) (-1) 1 (neg_ne_zero.mpr one_ne_zero)
    simpa [hf] using hh
  have hh : (-1 : K) = 1 := left_injective_1110 h 1 (hn.trans hs.symm)
  exact h2 (by linear_combination -hh)

/-- info: 'Definability.Homogeneous7041110.square_ne_neg_one_704' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square_ne_neg_one_704

/-- info: 'Definability.Homogeneous7041110.square_ne_neg_one_1110' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square_ne_neg_one_1110

end Definability.Homogeneous7041110
