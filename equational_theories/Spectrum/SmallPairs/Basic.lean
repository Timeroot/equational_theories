import equational_theories.Spectrum.Equation63.OrderTen.Normalization
import equational_theories.Equations.All

/-! Shared reductions for E670, E677, E704, E1279 and E1313. All have bijective
left translations. Right cancellation is also available for E1313, E704,
and E1279; the latter two additionally have bijective squaring. -/
namespace Spectrum.SmallPairs

inductive Kind where
  | e670 | e677 | e704 | e1279 | e1313
  deriving DecidableEq, Repr

def Kind.law : Kind → Law.NatMagmaLaw
  | .e670 => Law670
  | .e677 => Law677
  | .e704 => Law704
  | .e1279 => Law1279
  | .e1313 => Law1313

def first {A : Type*} (k : Kind) (x y : A) : A × A := match k with
  | .e670 => (x,y)
  | .e677 | .e1313 => (y,x)
  | .e704 | .e1279 => (x,x)

def right {A : Type*} (k : Kind) (x y : A) : A :=
  match k with | .e1313 => x | _ => y

def last {A : Type*} (k : Kind) (x y a : A) : A × A := match k with
  | .e670 | .e677 => (x,a)
  | .e704 => (y,a)
  | .e1279 | .e1313 => (a,y)

def middle {A : Type*} (k : Kind) (f : A → A → A) (x y : A) : A :=
  f (f (first k x y).1 (first k x y).2) (right k x y)

def Holds {A : Type*} (k : Kind) (f : A → A → A) : Prop :=
  ∀ x y, f y (f (last k x y (middle k f x y)).1
    (last k x y (middle k f x y)).2) = x

theorem holds_iff {A : Type*} (k : Kind) (M : Magma A) :
    Holds k M.op ↔ @satisfies _ A M k.law := by
  cases k <;> simp only [Kind.law, Law670.models_iff, Law677.models_iff,
    Law704.models_iff, Law1279.models_iff, Law1313.models_iff]
  all_goals unfold Holds middle first right last; exact forall_congr' fun _ => forall_congr' fun _ => eq_comm

theorem left_bijective {A : Type*} [Finite A] {k : Kind} {f : A → A → A}
    (h : Holds k f) (y : A) : Function.Bijective (f y) := by
  have hs : Function.Surjective (f y) := fun x =>
    ⟨f (last k x y (middle k f x y)).1 (last k x y (middle k f x y)).2, h x y⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

/-- For E704 and E1279, composing squaring with any right translation is
injective: the law provides an explicit left inverse for this composition. -/
theorem right_square_injective {A : Type*} {k : Kind} {f : A → A → A}
    (h : Holds k f) (hk : k = .e704 ∨ k = .e1279) (y : A) :
    Function.Injective (fun x => f (f x x) y) := by
  intro a b hab
  dsimp only at hab
  have ha := h a y
  have hb := h b y
  rcases hk with rfl | rfl
  · change f y (f y (f (f a a) y)) = a at ha
    change f y (f y (f (f b b) y)) = b at hb
    rw [hab] at ha
    exact ha.symm.trans hb
  · change f y (f (f (f a a) y) y) = a at ha
    change f y (f (f (f b b) y) y) = b at hb
    rw [hab] at ha
    exact ha.symm.trans hb

theorem square_bijective {A : Type*} [Finite A] {k : Kind} {f : A → A → A}
    (h : Holds k f) (hk : k = .e704 ∨ k = .e1279) :
    Function.Bijective (fun x => f x x) := by
  have hi : Function.Injective (fun x => f x x) := fun a b hab =>
    right_square_injective h hk a (congrArg (fun z => f z a) hab)
  exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

theorem right_bijective {A : Type*} [Finite A] {k : Kind} {f : A → A → A}
    (h : Holds k f) (hk : k = .e704 ∨ k = .e1279) (y : A) :
    Function.Bijective (fun x => f x y) := by
  have hi : Function.Injective (fun x => f x y) := by
    intro a b hab
    obtain ⟨u,hu⟩ := (square_bijective h hk).2 a
    obtain ⟨v,hv⟩ := (square_bijective h hk).2 b
    have he : u = v := right_square_injective h hk y (by
      dsimp only at hu hv hab ⊢
      rw [hu, hv]
      exact hab)
    exact hu.symm.trans ((congrArg (fun z => f z z) he).trans hv)
  exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

theorem right_bijective1313 {A : Type*} [Finite A] {f : A → A → A}
    (h : Holds .e1313 f) (y : A) : Function.Bijective (fun x => f x y) := by
  have hs : Function.Surjective (fun x => f x y) := by
    intro z
    refine ⟨middle .e1313 f (f y z) y, ?_⟩
    apply (left_bijective h y).1
    exact h (f y z) y
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem right_bijective_of_kind {A : Type*} [Finite A] {k : Kind} {f : A → A → A}
    (h : Holds k f) (hk : k = .e704 ∨ k = .e1279 ∨ k = .e1313) (y : A) :
    Function.Bijective (fun x => f x y) := by
  rcases hk with hk | hk | rfl
  · exact right_bijective h (Or.inl hk) y
  · exact right_bijective h (Or.inr hk) y
  · exact right_bijective1313 h y

theorem holds_relabel {A : Type*} {k : Kind} {f : A → A → A}
    (h : Holds k f) (e : A ≃ A) : Holds k (fun x y => e (f (e.symm x) (e.symm y))) := by
  cases k <;> intro x y <;> simp only [Holds, middle, first, right, last] at h ⊢
  all_goals simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    using congrArg e (h (e.symm x) (e.symm y))

/-- Normalize a model by selecting a non-idempotent 0 if one exists, then
labelling the cycles of its left translation consecutively. Both steps are
proved for arbitrary sizes; no permutations are enumerated. -/
theorem normalized {n : ℕ} [NeZero n] {k : Kind}
    (f : Fin n → Fin n → Fin n) (h : Holds k f) :
    ∃ g : Fin n → Fin n → Fin n, Holds k g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) ∧ (∀ y, (g 0 y).val ≤ y.val + 1) := by
  classical
  have choose_zero : ∃ g : Fin n → Fin n → Fin n, Holds k g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) := by
    by_cases hi : ∀ x, f x x = x
    · exact ⟨f, h, fun _ => hi⟩
    · push Not at hi
      obtain ⟨x, hx⟩ := hi
      let e := Equiv.swap x (0 : Fin n)
      let g (a b : Fin n) := e (f (e.symm a) (e.symm b))
      refine ⟨g, holds_relabel h e, fun hg => ?_⟩
      have he : e.symm 0 = x := Equiv.swap_apply_right x 0
      have : f x x = x := by
        apply e.injective
        simpa only [g, he, e, Equiv.swap_apply_left] using hg
      exact (hx this).elim
  obtain ⟨g, hg, hi⟩ := choose_zero
  obtain ⟨e, he, hc⟩ := E63.OrderTen.exists_chain_label (g 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let q (a b : Fin n) := e (g (e.symm a) (e.symm b))
  refine ⟨q, holds_relabel hg e, ?_, ?_⟩
  · intro hq x
    have h0 : g 0 0 = 0 := by
      apply e.injective
      simpa only [q, he', he] using hq
    simp only [q, hi h0, Equiv.apply_symm_apply]
  · intro y
    simpa only [q, he'] using hc y

end Spectrum.SmallPairs
