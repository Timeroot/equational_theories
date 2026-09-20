import equational_theories.Definability.Linear
import equational_theories.Definability.CloneTraps

/-!
# Twisted finite obstructions to term recovery

The common family on `ZMod p × ZMod q` is
`(x,u) □ (y,v) = (a*x + (1-a)*y, b*u + (1-b)*v + c*w(x,y))`.
A multiplicative interpolation identity for `w` makes this family closed under
terms of any member with `c = 1`. In each example the target forces `c = 0`,
so every target companion preserves the zero section. The source does not,
which prevents term recovery. All finite checks use kernel `decide`.
-/

open Law Law.MagmaLaw Magma

namespace TwistedRecovery

section Family

variable {p q : ℕ}

abbrev Carrier (p q : ℕ) := ZMod p × ZMod q

@[implicit_reducible]
def family (w : ZMod p → ZMod p → ZMod q) (a : ZMod p) (b c : ZMod q) :
    Magma (Carrier p q) :=
  ⟨fun x y => (a * x.1 + (1 - a) * y.1,
    b * x.2 + (1 - b) * y.2 + c * w x.1 y.1)⟩

@[simp] theorem family_op (w : ZMod p → ZMod p → ZMod q)
    (a : ZMod p) (b c : ZMod q) (x y : Carrier p q) :
    (family w a b c).op x y = (a * x.1 + (1 - a) * y.1,
      b * x.2 + (1 - b) * y.2 + c * w x.1 y.1) := rfl

/-- This identity is the only condition on the twist needed for closure. -/
def Interpolates (w : ZMod p → ZMod p → ZMod q) : Prop :=
  ∀ a a' x y, w (a * x + (1 - a) * y) (a' * x + (1 - a') * y) =
    w a a' * w x y

def Family (w : ZMod p → ZMod p → ZMod q)
    (f : Carrier p q → Carrier p q → Carrier p q) : Prop :=
  ∃ a b c, f = (family w a b c).op

theorem family_invariant (w : ZMod p → ZMod p → ZMod q) (hw : Interpolates w)
    (A : ZMod p) (B : ZMod q) :
    (family w A B 1).IsCloneInvariant (Family w) where
  fst := ⟨1, 1, 0, by funext x y; simp⟩
  snd := ⟨0, 0, 0, by funext x y; simp⟩
  comp := by
    rintro f g ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    refine ⟨A * a + (1 - A) * a', B * b + (1 - B) * b',
      B * c + (1 - B) * c' + w a a', ?_⟩
    funext x y
    apply Prod.ext
    · simp only [family_op]
      ring
    · simp only [family_op]
      rw [hw]
      ring

def PreservesSection (f : Carrier p q → Carrier p q → Carrier p q) : Prop :=
  ∀ x y, x.2 = 0 → y.2 = 0 → (f x y).2 = 0

theorem section_invariant {N : Magma (Carrier p q)} (h : PreservesSection N.op) :
    N.IsCloneInvariant PreservesSection where
  fst := fun _ _ hx _ => hx
  snd := fun _ _ _ hy => hy
  comp := fun _ _ hf hg x y hx hy => h _ _ (hf x y hx hy) (hg x y hx hy)

/-- A target that erases every twist cannot recover a nonzero source twist. -/
theorem not_termStructuralFromFin_of_twist [NeZero p] [NeZero q]
    {L L' : NatMagmaLaw} (w : ZMod p → ZMod p → ZMod q)
    (A : ZMod p) (B : ZMod q) (hw : Interpolates w)
    (hne : ∃ x y, w x y ≠ 0)
    (hsource : @satisfies _ (Carrier p q) (family w A B 1) L')
    (htarget : ∀ a b c, @satisfies _ (Carrier p q) (family w a b c) L → c = 0) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨N, hN, hfwd, hback⟩ := h (family w A B 1) hsource
  obtain ⟨a, b, c, hop⟩ := (family_invariant w hw A B).of_termDefinable hfwd
  have hEq : N = family w a b c := by
    cases N
    exact congrArg Magma.mk hop
  subst N
  have hc := htarget a b c hN
  subst c
  have hs : PreservesSection (family w a b 0).op := by
    intro x y hx hy
    simp [hx, hy]
  have hbackSection := (section_invariant hs).of_termDefinable hback
  obtain ⟨x, y, hxy⟩ := hne
  exact hxy (by simpa using hbackSection (x, 0) (y, 0) rfl rfl)

end Family

namespace E1516

/-- The nonzero indicator on `F₅`, valued in `F₇`. -/
def twist (x y : ZMod 5) : ZMod 7 := if x = y then 0 else 1

abbrev source : Magma (Carrier 5 7) := family twist 3 6 1

theorem interpolates : Interpolates twist := by unfold Interpolates; decide

theorem source_law : @Equation1516 (Carrier 5 7) source := by decide

/-- One instance of E1489 already forces the twist to vanish. -/
theorem target_no_twist (a : ZMod 5) (b c : ZMod 7)
    (h : @Equation1489 (Carrier 5 7) (family twist a b c)) : c = 0 := by
  have check : ∀ (a : ZMod 5) (b c : ZMod 7),
      (1, 0) = (family twist a b c).op ((family twist a b c).op (0, 0) (1, 0))
        ((family twist a b c).op (0, 0) ((family twist a b c).op (1, 0) (0, 0))) →
      c = 0 := by decide
  exact check a b c (h (1, 0) (0, 0))

end E1516

namespace E1076

/-- The quadratic character of `F₅`, valued in `F₁₃`. -/
def character (x : ZMod 5) : ZMod 13 :=
  match x.val with
  | 0 => 0
  | 1 | 4 => 1
  | _ => -1

def twist (x y : ZMod 5) : ZMod 13 := character (x - y)

abbrev source : Magma (Carrier 5 13) := family twist 4 7 1

theorem interpolates : Interpolates twist := by unfold Interpolates; decide

set_option maxRecDepth 10000 in
theorem source_law : @Equation1076 (Carrier 5 13) source := by decide

/-- Two instances suffice; the finite check ranges over 845 parameter triples. -/
theorem target_no_twist (a : ZMod 5) (b c : ZMod 13)
    (h : @Equation1313 (Carrier 5 13) (family twist a b c)) : c = 0 := by
  have check : ∀ (a : ZMod 5) (b c : ZMod 13),
      (1, 0) = (family twist a b c).op (0, 0)
        ((family twist a b c).op
          ((family twist a b c).op ((family twist a b c).op (0, 0) (1, 0)) (1, 0))
          (0, 0)) →
      (0, 1) = (family twist a b c).op (0, 0)
        ((family twist a b c).op
          ((family twist a b c).op ((family twist a b c).op (0, 0) (0, 1)) (0, 1))
          (0, 0)) → c = 0 := by decide
  exact check a b c (h (1, 0) (0, 0)) (h (0, 1) (0, 0))

end E1076

namespace E1685

/-- The quadratic character of `F₇`, valued in `F₅`. -/
def character (x : ZMod 7) : ZMod 5 :=
  match x.val with
  | 0 => 0
  | 1 | 2 | 4 => 1
  | _ => -1

def twist (x y : ZMod 7) : ZMod 5 := character (x - y)

abbrev source : Magma (Carrier 7 5) := family twist 2 3 1

theorem interpolates : Interpolates twist := by unfold Interpolates; decide

theorem source_law : @Equation1685 (Carrier 7 5) source := by decide

/-- The target is tested on a base direction and a fiber direction. -/
theorem target_no_twist (a : ZMod 7) (b c : ZMod 5)
    (h : @Equation3548 (Carrier 7 5) (family twist a b c)) : c = 0 := by
  have check : ∀ (a : ZMod 7) (b c : ZMod 5),
      (family twist a b c).op (1, 0) (0, 0) =
        (family twist a b c).op (0, 0)
          ((family twist a b c).op ((family twist a b c).op (1, 0) (0, 0)) (1, 0)) →
      (family twist a b c).op (0, 1) (0, 0) =
        (family twist a b c).op (0, 0)
          ((family twist a b c).op ((family twist a b c).op (0, 1) (0, 0)) (0, 1)) →
      c = 0 := by decide
  exact check a b c (h (1, 0) (0, 0)) (h (0, 1) (0, 0))

end E1685

end TwistedRecovery

open TwistedRecovery

theorem Equation1489_not_termStructuralFromFin_Equation1516_twisted :
    ¬ Law1489.TermStructuralFromFin Law1516 :=
  not_termStructuralFromFin_of_twist E1516.twist 3 6 E1516.interpolates
    ⟨0, 1, by decide⟩
    ((@Law1516.models_iff _ E1516.source).mpr E1516.source_law)
    fun a b c h => E1516.target_no_twist a b c
      ((@Law1489.models_iff _ (family E1516.twist a b c)).mp h)

theorem Equation1313_not_termStructuralFromFin_Equation1076_twisted :
    ¬ Law1313.TermStructuralFromFin Law1076 :=
  not_termStructuralFromFin_of_twist E1076.twist 4 7 E1076.interpolates
    ⟨1, 0, by decide⟩
    ((@Law1076.models_iff _ E1076.source).mpr E1076.source_law)
    fun a b c h => E1076.target_no_twist a b c
      ((@Law1313.models_iff _ (family E1076.twist a b c)).mp h)

theorem Equation3548_not_termStructuralFromFin_Equation1685_twisted :
    ¬ Law3548.TermStructuralFromFin Law1685 :=
  not_termStructuralFromFin_of_twist E1685.twist 2 3 E1685.interpolates
    ⟨1, 0, by decide⟩
    ((@Law1685.models_iff _ E1685.source).mpr E1685.source_law)
    fun a b c h => E1685.target_no_twist a b c
      ((@Law3548.models_iff _ (family E1685.twist a b c)).mp h)

/-- info: 'Equation1489_not_termStructuralFromFin_Equation1516_twisted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation1489_not_termStructuralFromFin_Equation1516_twisted

/-- info: 'Equation1313_not_termStructuralFromFin_Equation1076_twisted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation1313_not_termStructuralFromFin_Equation1076_twisted

/-- info: 'Equation3548_not_termStructuralFromFin_Equation1685_twisted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation3548_not_termStructuralFromFin_Equation1685_twisted
