import equational_theories.Spectrum.SmallPairs.Basic

/-! Small-order reductions for identities with three operations nested below
an outer left translation. No right cancellation or idempotence is assumed. -/
namespace Spectrum.SmallOrders

inductive Kind where
  | e467 | e670 | e677 | e704 | e1076 | e1083 | e1110 | e1279 | e1286 | e1313
  deriving DecidableEq, Repr

def Kind.law : Kind → Law.NatMagmaLaw
  | .e467 => Law467
  | .e670 => Law670
  | .e677 => Law677
  | .e704 => Law704
  | .e1076 => Law1076
  | .e1083 => Law1083
  | .e1110 => Law1110
  | .e1279 => Law1279
  | .e1286 => Law1286
  | .e1313 => Law1313

def first {A : Type*} (k : Kind) (x y : A) : A × A := match k with
  | .e467 => (y,y)
  | .e670 | .e1076 | .e1286 => (x,y)
  | .e677 | .e1083 | .e1313 => (y,x)
  | .e704 | .e1110 | .e1279 => (x,x)

def inner {A : Type*} (k : Kind) (x y a : A) : A × A := match k with
  | .e467 | .e1076 | .e1083 => (x,a)
  | .e1110 => (y,a)
  | .e1286 | .e1313 => (a,x)
  | .e670 | .e677 | .e704 | .e1279 => (a,y)

def last {A : Type*} (k : Kind) (x y a : A) : A × A := match k with
  | .e467 | .e670 | .e677 => (x,a)
  | .e704 => (y,a)
  | .e1076 | .e1083 | .e1110 | .e1279 | .e1286 | .e1313 => (a,y)

def middle {A : Type*} (k : Kind) (f : A → A → A) (x y : A) : A :=
  let a := f (first k x y).1 (first k x y).2
  f (inner k x y a).1 (inner k x y a).2

def Holds {A : Type*} (k : Kind) (f : A → A → A) : Prop :=
  ∀ x y, f y (f (last k x y (middle k f x y)).1
    (last k x y (middle k f x y)).2) = x

theorem holds_iff {A : Type*} (k : Kind) (M : Magma A) :
    Holds k M.op ↔ @satisfies _ A M k.law := by
  cases k <;> simp only [Kind.law, Law467.models_iff, Law670.models_iff, Law677.models_iff, Law704.models_iff, Law1076.models_iff, Law1083.models_iff, Law1110.models_iff, Law1279.models_iff, Law1286.models_iff, Law1313.models_iff]
  all_goals unfold Holds middle first inner last; exact forall_congr' fun _ => forall_congr' fun _ => eq_comm

theorem left_bijective {A : Type*} [Finite A] {k : Kind} {f : A → A → A}
    (h : Holds k f) (y : A) : Function.Bijective (f y) := by
  have hs : Function.Surjective (f y) := fun x =>
    ⟨f (last k x y (middle k f x y)).1 (last k x y (middle k f x y)).2, h x y⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

/-- These identities also force bijective right translations. -/
def rightLatin : Kind → Bool
  | .e704 | .e1076 | .e1083 | .e1110 | .e1279 | .e1286 | .e1313 => true
  | _ => false

theorem right_bijective {A : Type*} [Finite A] {k : Kind} {f : A → A → A}
    (h : Holds k f) (hk : rightLatin k = true) (y : A) :
    Function.Bijective (fun x => f x y) := by
  by_cases h704 : k = .e704
  · subst k
    exact SmallPairs.right_bijective (k := .e704) (f := f) h (Or.inl rfl) y
  have hl (x a : A) : last k x y a = (a,y) := by
    cases k <;> simp_all [rightLatin, last]
  have hs : Function.Surjective (fun x => f x y) := by
    intro z
    refine ⟨middle k f (f y z) y, ?_⟩
    apply (left_bijective h y).1
    simpa only [hl] using h (f y z) y
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

/-- If the only occurrences of the first variable are its square, the law
supplies a left inverse to squaring. -/
def squareLatin : Kind → Bool
  | .e704 | .e1110 | .e1279 => true
  | _ => false

theorem square_bijective {A : Type*} [Finite A] {k : Kind} {f : A → A → A}
    (h : Holds k f) (hk : squareLatin k = true) :
    Function.Bijective (fun x => f x x) := by
  have hi : Function.Injective (fun x => f x x) := by
    intro a b hab
    have ha := h a a
    have hb := h b a
    cases k <;> simp_all [squareLatin, Holds, middle, first, inner, last]
  exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

def innerRecover : Kind → Bool
  | .e670 | .e677 => false
  | _ => true

theorem inner_injective {A : Type*} [Finite A] {k : Kind} {f : A → A → A}
    (h : Holds k f) (hk : innerRecover k = true) (x y : A) :
    Function.Injective (fun a => f (inner k x y a).1 (inner k x y a).2) := by
  cases k <;> simp only [innerRecover] at hk
  all_goals try contradiction
  all_goals first
    | exact (left_bijective h x).1
    | exact (left_bijective h y).1
    | exact (right_bijective h rfl x).1
    | exact (right_bijective h rfl y).1

theorem last_injective {A : Type*} [Finite A] {k : Kind} {f : A → A → A}
    (h : Holds k f) (x y : A) :
    Function.Injective (fun a => f (last k x y a).1 (last k x y a).2) := by
  cases k
  all_goals first
    | exact (left_bijective h x).1
    | exact (left_bijective h y).1
    | exact (right_bijective h rfl y).1

theorem holds_relabel {A : Type*} {k : Kind} {f : A → A → A}
    (h : Holds k f) (e : A ≃ A) : Holds k (fun x y => e (f (e.symm x) (e.symm y))) := by
  cases k <;> intro x y <;> simp only [Holds, middle, first, inner, last] at h ⊢
  all_goals simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    using congrArg e (h (e.symm x) (e.symm y))

/-- Choose a non-idempotent zero if possible, then label the cycles of its
left translation consecutively. Both reductions preserve all models. -/
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


end Spectrum.SmallOrders
