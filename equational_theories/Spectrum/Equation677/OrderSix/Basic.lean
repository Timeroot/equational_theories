import equational_theories.ManuallyProved.Equation677
import Mathlib.Data.Finite.Card

/-! The equational order-six exclusion contributed in PR #6, ported to the
project's magma laws and Mathlib finiteness. The generated case analyses are
ordinary equality proofs, with no model-search oracle or admission. -/
namespace Spectrum.E677.OrderSix
universe u
local infixl:70 " * " => Magma.op

def Eq255At {M : Type u} [Magma M] (a : M) : Prop := a * a * a * a = a
abbrev Idempotent {M : Type u} [Magma M] (a : M) : Prop := a * a = a

theorem Idempotent.eq {M : Type u} [Magma M] {a : M} (h : Idempotent a) : a * a = a := h

theorem exists_notMem {α : Type*} [Finite α] {l : List α}
    (hl : l.length < Nat.card α) : ∃ x, x ∉ l := by
  classical
  letI := Fintype.ofFinite α
  by_contra! h
  have hu : l.toFinset = Finset.univ := Finset.ext (by simpa using h)
  have hc := List.toFinset_card_le l
  rw [hu, Finset.card_univ, ← Nat.card_eq_fintype_card] at hc
  omega

theorem span_six {α : Type*} [Finite α] (hM : Nat.card α = 6) {a b c d e f : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) (z : α) :
    z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f := by
  classical
  letI := Fintype.ofFinite α
  have hnd : [a,b,c,d,e,f].Nodup := by
    simp [List.nodup_cons, hab,hac,had,hae,haf,hbc,hbd,hbe,hbf,hcd,hce,hcf,hde,hdf,hef]
  have hc : [a,b,c,d,e,f].toFinset.card = Fintype.card α := by
    rw [List.toFinset_card_of_nodup hnd, ← Nat.card_eq_fintype_card, hM]; rfl
  have hz : z ∈ [a,b,c,d,e,f].toFinset := by rw [Finset.eq_univ_of_card _ hc]; exact Finset.mem_univ _
  simpa using hz

/-- **Left division**, $a / b := a \diamond ((b \diamond a) \diamond b)$. Equation 677 says
exactly that $b \diamond (a / b) = a$ (`Spectrum.E677.OrderSix.mul_div`); on a finite carrier $a / b$ is
therefore the unique solution of $L_b(x) = a$, that is $a / b = L_b^{-1}(a)$
(`Spectrum.E677.OrderSix.div_eq_iff_mul_eq`). The instance is scoped to the namespace `Spectrum.E677.OrderSix`. -/
scoped instance instDiv {M : Type u} [Magma M] [Fact (Equation677 M)] : Div M :=
  ⟨fun a b => a * (b * a * b)⟩

section Mul

variable {M : Type u} [Magma M] [Fact (Equation677 M)]

/-- Equation 677, oriented for rewriting:
$b \diamond (a \diamond ((b \diamond a) \diamond b)) = a$. -/
theorem eq677 (a b : M) : b * (a * (b * a * b)) = a :=
  ((Fact.out : Equation677 M) a b).symm

theorem div_def (a b : M) : a / b = a * (b * a * b) :=
  rfl

/-- $L_b(a / b) = a$: Equation 677 itself, so every $L_b$ is onto. -/
theorem mul_div (a b : M) : b * (a / b) = a :=
  eq677 a b

end Mul

section Finite

variable {M : Type u} [Magma M] [Fact (Equation677 M)] [Finite M]

/-- **Left cancellation**: $L_a$ is injective. The map $x \mapsto x / a$ is injective, because
$L_a(x / a) = x$; so it lists $|M|$ distinct values and is onto. Every element is therefore some
$x / a$, and $L_a(x / a) = x$ recovers $x$. -/
theorem mul_left_cancel {a b c : M} (h : a * b = a * c) : b = c :=
  Eq677.eq677_left_cancel (Fact.out : Equation677 M) a h

/-- The defining property of left division: $a / b = c \iff b \diamond c = a$. -/
theorem div_eq_iff_mul_eq {a b c : M} : a / b = c ↔ b * c = a :=
  ⟨fun h => h ▸ mul_div a b, fun h => mul_left_cancel ((mul_div a b).trans h.symm)⟩

theorem mul_div_cancel_left {a b : M} : a * b / a = b :=
  div_eq_iff_mul_eq.mpr rfl

/-- **The identity of the division calculus**: $a / b / a = (b \diamond a) \diamond b$. -/
theorem div_div_eq_mul_mul {a b : M} : a / b / a = b * a * b :=
  div_eq_iff_mul_eq.mpr rfl

theorem mul_mul_eq_div_div {a b : M} : b * a * b = a / b / a :=
  div_div_eq_mul_mul.symm

/-- **Every product is a division of its two backward steps**:
$a \diamond b = (a / b / b) / (a / b)$. This is `div_div_eq_mul_mul` read at the pair
$(a / b, b)$. -/
theorem mul_eq_div_div_div (a b : M) : a * b = a / b / b / (a / b) := by
  have h := div_div_eq_mul_mul (a := a / b) (b := b)
  rw [mul_div] at h
  exact h.symm

/-! ### Left units -/

/-- If $b$ is a left unit for $a$, i.e. $R_a(b) = a$, then $a \diamond (a \diamond b) = a$. -/
theorem mul_mul_eq_self_of_mul_eq {a b : M} (h : b * a = a) : a * (a * b) = a := by
  have h₁ := eq677 a b
  rw [h] at h₁
  exact mul_left_cancel (h₁.trans h.symm)

/-- **A left unit is the cube**: $b \diamond a = a$ forces $b = (a \diamond a) \diamond a$. -/
theorem eq_cube_of_mul_eq {a b : M} (h : b * a = a) : b = a * a * a :=
  mul_left_cancel (mul_left_cancel ((mul_mul_eq_self_of_mul_eq h).trans (eq677 a a).symm))

/-- **Equation 255 at $a$ is the existence of a left unit for $a$** (one direction). -/
theorem eq255At_of_exists_mul_eq {a : M} (h : ∃ b, b * a = a) : Eq255At a := by
  obtain ⟨b, hb⟩ := h
  have hc := eq_cube_of_mul_eq hb
  rw [hc] at hb
  exact hb

/-- **The cube is the predecessor times the successor**:
$(a / a) \diamond (a \diamond a) = (a \diamond a) \diamond a$. -/
theorem div_self_mul_sq (a : M) : a / a * (a * a) = a * a * a := by
  have h₁ : a / a / a = a * a * a := div_div_eq_mul_mul
  have h₂ : a / a / a / (a / a) = a * (a / a) * a := div_div_eq_mul_mul
  rw [h₁, mul_div] at h₂
  exact div_eq_iff_mul_eq.mp h₂

/-! ### Idempotents

Several one-variable identities weaker than $a \diamond a = a$ already force it, and a product
$a \diamond b$ with $b \neq a$ avoids its factors and its backward steps, given idempotency at
the element the proof cancels against. -/

/-- An idempotent absorbs nothing: $a \diamond b = a$ forces $b = a$. -/
theorem eq_of_mul_eq_self_left {a b : M} (ha : Idempotent a) (h : a * b = a) : b = a :=
  mul_left_cancel (h.trans ha.symm)

/-- An idempotent has no left unit but itself: $a \diamond b = b$ forces $a = b$. -/
theorem eq_of_mul_eq_self_right {a b : M} (hb : Idempotent b) (h : a * b = b) :
    a = b := by
  have hc := eq_cube_of_mul_eq h
  rwa [hb, hb] at hc

/-- **A product equal to its backward step collapses**: $a \diamond b = a / b$ forces $a = b$,
provided $a / b$ is idempotent. -/
theorem eq_of_mul_eq_div {a b : M} (hu : Idempotent (a / b)) (h : a * b = a / b) :
    a = b := by
  have h2 : a / b / b / (a / b) = a / b := (mul_eq_div_div_div a b).symm.trans h
  have h3 : a / b / b = a / b := (div_eq_iff_mul_eq.mp h2).symm.trans hu
  have h5 : b = a / b := by
    have hc := eq_cube_of_mul_eq (div_eq_iff_mul_eq.mp h3)
    rwa [hu, hu] at hc
  have h6 : a = a / b := by
    have h7 := mul_div (a / b) b
    rw [h3] at h7
    exact (mul_div a b).symm.trans h7
  exact h6.trans h5.symm

/-- **A product equal to its second backward step collapses**: $a \diamond b = a / b / b$
forces $a = b$, provided $a / b / b$ is idempotent. -/
theorem eq_of_mul_eq_div_div {a b : M} (hv : Idempotent (a / b / b))
    (h : a * b = a / b / b) : a = b := by
  have h2 : a / b / b / (a / b) = a / b / b := (mul_eq_div_div_div a b).symm.trans h
  have h4 : a / b = a / b / b := by
    have hc := eq_cube_of_mul_eq (div_eq_iff_mul_eq.mp h2)
    rwa [hv, hv] at hc
  have h5 : a = a / b :=
    calc a = b * (a / b) := (mul_div a b).symm
      _ = b * (a / b / b) := by rw [← h4]
      _ = a / b := mul_div (a / b) b
  have ha : Idempotent a := by
    have hchain : a = a / b / b := h5.trans h4
    rw [hchain]
    exact hv
  have h6 : b * a = a := (congrArg (b * ·) h5).trans (mul_div a b)
  have hc := eq_cube_of_mul_eq h6
  rw [ha, ha] at hc
  exact hc.symm

/-- $(a \diamond a) \diamond a = a$ forces $a$ to be idempotent. -/
theorem isIdempotentElem_of_cube_eq_self {a : M} (h : a * a * a = a) : Idempotent a :=
  (eq_cube_of_mul_eq h).trans h

/-- $a \diamond (a \diamond a) = a$ forces $a$ to be idempotent. -/
theorem isIdempotentElem_of_mul_sq {a : M} (h : a * (a * a) = a) : Idempotent a := by
  have h₁ : a / a = a * a := div_eq_iff_mul_eq.mpr h
  rw [div_def] at h₁
  exact isIdempotentElem_of_cube_eq_self (mul_left_cancel h₁)

/-- $(a \diamond a) \diamond (a \diamond a) = a$ forces $a$ to be idempotent. -/
theorem isIdempotentElem_of_sq_mul_sq {a : M} (h : a * a * (a * a) = a) :
    Idempotent a := by
  have h₁ : a / (a * a) = a * a := div_eq_iff_mul_eq.mpr h
  have h₂ : a * a / a = a := mul_div_cancel_left
  have h₃ : a * (a * a) * a = a * a := by
    have h' := div_div_eq_mul_mul (a := a * a) (b := a)
    rw [h₂, h₁] at h'
    exact h'.symm
  have h₄ : a * (a * (a * a)) * a = a := by
    have h' := div_div_eq_mul_mul (a := a * (a * a)) (b := a)
    rw [mul_div_cancel_left] at h'
    exact mul_left_cancel ((div_eq_iff_mul_eq.mp h').trans h₃.symm)
  have h₅ : a * (a * (a * a)) = a * a * a := eq_cube_of_mul_eq h₄
  have h₆ : a * a * a * (a * a) = a := by
    have h' := div_div_eq_mul_mul (a := a) (b := a * a)
    rw [h₁, h₂] at h'
    exact h'.symm
  rw [h₅] at h₄
  exact (mul_left_cancel (h₄.trans h₆.symm)).symm

/-- $a \diamond (a \diamond (a \diamond a)) = a$ forces $a$ to be idempotent. -/
theorem isIdempotentElem_of_mul_mul_sq {a : M} (h : a * (a * (a * a)) = a) :
    Idempotent a := by
  have hpa : a * (a * a) / a = a * a := div_eq_iff_mul_eq.mpr rfl
  have h₁ : a * a * a = a * a := by
    have h' : a / a = a * (a * a) := div_eq_iff_mul_eq.mpr h
    rw [div_def] at h'
    exact mul_left_cancel h'
  have h₂ : a * (a * a) * (a * a) = a * a := by
    have h' := div_div_eq_mul_mul (a := a * (a * a)) (b := a)
    rw [hpa, h] at h'
    exact div_eq_iff_mul_eq.mp h'
  have h₃ : a * (a * a) = a * a * (a * a) * (a * a) := eq_cube_of_mul_eq h₂
  have h₄ : a * a / (a * a) = a := div_eq_iff_mul_eq.mpr h₁
  have h₅ : a / (a * a) = a * (a * a) := by
    have h' := div_div_eq_mul_mul (a := a * a) (b := a * a)
    rw [h₄] at h'
    exact h'.trans h₃.symm
  have h₆ : a * a * (a * a) = a * a := by
    have h' := div_div_eq_mul_mul (a := a) (b := a * a)
    rw [h₅, hpa, h₁] at h'
    exact h'.symm
  exact mul_left_cancel (by rw [h₃, h₆, h₆] : a * (a * a) = a * a)

/-- Under Equation 255 at $a$, $a \diamond (a \diamond a) = (a \diamond a) \diamond a$ forces
$a$ to be idempotent. -/
theorem isIdempotentElem_of_mul_sq_eq_sq_mul {a : M} (h255 : Eq255At a)
    (h : a * (a * a) = a * a * a) : Idempotent a := by
  have h₁ : a / (a * a) = a := by
    have h' := div_div_eq_mul_mul (a := a * a) (b := a)
    rw [mul_div_cancel_left, h, h255] at h'
    exact h'
  exact isIdempotentElem_of_cube_eq_self (div_eq_iff_mul_eq.mp h₁)

/-- Under Equation 255 at $a$,
$a \diamond (a \diamond (a \diamond a)) = (a \diamond a) \diamond a$ forces $a$ to be
idempotent. -/
theorem isIdempotentElem_of_mul_mul_sq_eq_cube {a : M} (h255 : Eq255At a)
    (h : a * (a * (a * a)) = a * a * a) : Idempotent a := by
  have h₁ : a * (a * a) * a = a * a := by
    have e := eq677 (a * (a * a)) a
    rw [show a * (a * (a * a)) * a = a from by rw [h]; exact h255] at e
    exact mul_left_cancel e
  have e₂ := eq677 (a * a) a
  rw [h₁] at e₂
  exact isIdempotentElem_of_sq_mul_sq (mul_left_cancel e₂)

/-! ### Separation -/

/-- $(x \diamond (x \diamond a)) \diamond x = a / (x \diamond a)$. -/
theorem mul_mul_mul_eq_div (x a : M) : x * (x * a) * x = a / (x * a) := by
  rw [mul_mul_eq_div_div, mul_div_cancel_left]

/-- A single agreement $y \diamond a = x \diamond a$ forces
$(y \diamond (y \diamond a)) \diamond y = (x \diamond (x \diamond a)) \diamond x$. -/
theorem mul_mul_mul_eq_of_mul_eq {x y a : M} (h : y * a = x * a) :
    y * (y * a) * y = x * (x * a) * x := by
  rw [mul_mul_mul_eq_div, mul_mul_mul_eq_div, h]

/-- **The separation lemma**: two left translations agreeing at $a$ and at $L_x(a)$ are equal,
$L_y(a) = L_x(a)$ and $L_y(L_x(a)) = L_x(L_x(a))$ force $y = x$. -/
theorem eq_of_mul_eq_of_mul_mul_eq {x y a : M} (h₁ : y * a = x * a)
    (h₂ : y * (x * a) = x * (x * a)) : y = x := by
  have h := mul_mul_mul_eq_of_mul_eq h₁
  rw [h₁, h₂] at h
  exact mul_left_cancel h

end Finite


end Spectrum.E677.OrderSix
