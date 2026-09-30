/-!
# No magma of order six satisfies Equation 677

A self-contained Lean 4 file. It uses nothing but Lean's core library — no Mathlib, no
Batteries, no `lake` project — and compiles with a bare `lean Order6.lean`.

Write $x \diamond y$ for the magma operation (in Lean, `x * y` through the core `Mul` class),
and write
$$L_a \colon x \mapsto a \diamond x, \qquad R_a \colon x \mapsto x \diamond a$$
for the left and right translations. Equation 677 of the Equational Theories Project is
$$x = y \diamond (x \diamond ((y \diamond x) \diamond y)), \tag{677}$$
and Equation 255 is $x = ((x \diamond x) \diamond x) \diamond x$. Whether (677) implies (255)
on finite magmas is the last open finite implication of the project.

The main theorem, `Magma677.card_ne_six`, says that **a finite magma satisfying (677) never
has exactly six elements**. `Magma677.no_order_six` restates it with an explicit enumeration of
the carrier, and `Magma677.no_op_on_fin_six` for binary operations on `Fin 6`.

## The shape of the proof

The proof is the argument of the `Eq677255` library (`Eq677255.OrderSix`), rebuilt on core
Lean. It is a chain of equational deductions: nothing is searched at proof time, and `decide`
is used only for inequalities between small numerals and for the enumeration of `Fin 6`.

1. **The division calculus.** Put $a / b := a \diamond ((b \diamond a) \diamond b)$. Then (677)
   reads $b \diamond (a / b) = a$, so every $L_b$ is onto; on a finite carrier it is a
   bijection with $L_b^{-1}(a) = a / b$. The one identity with content is
   $$a / b / a = (b \diamond a) \diamond b,$$
   and together with left cancellation it drives everything below.
2. **The degree.** The degree of $a$ is the length of the cycle of $L_a$ through $a$: the least
   $n > 0$ with $L_a^n(a) = a$. Degree $1$ is idempotence, degrees $2$ and $3$ never occur, and
   an element satisfying (255) has degree neither $4$ nor $5$. The cycle of $a$ ends
   $\dots, (a \diamond a) \diamond a,\ a / a,\ a$: its last two points before $a$ are the cube and
   $a / a$.
3. **At order six every element is idempotent.** A non-idempotent element has degree $4$, $5$ or
   $6$. Degree $6$ is refuted by a case analysis over the cells of the table. A fixed point
   $m \neq a$ of $L_a$ is then impossible: $a$ is a left unit of $m$, hence
   $a = (m \diamond m) \diamond m$, hence $m$ satisfies (255), is not idempotent, and so has degree
   $6$. In degree $5$ the one point the cycle misses is fixed by $L_a$; in degree $4$ the two
   missed points are fixed or swapped, and the swap is refuted by a second case analysis.
4. **No six-element magma satisfies (677) and the idempotent law.** Off the diagonal a product
   avoids both factors and both backward steps $a / b$, $a / b / b$; a third case analysis
   refutes every remaining table.

The three case analyses were machine-generated from a propagating search; every step is an
instance of (677), a left cancellation, or one of the lemmas proved in the first half of the
file. In their comments a line such as `-- $c \diamond a = d$` names the branch in which the
cell $c \diamond a$ takes the value $d$.

## Conventions

* Lean's `a * b * c` is $(a \diamond b) \diamond c$: products associate to the left.
* Finiteness is the class `Finite` below — some duplicate-free list enumerates the carrier —
  and `Finite.card` is the length of such a list, standing in for Mathlib's `Finite` and
  `Nat.card`.
-/

universe u

/-! ## Finite types

Core Lean has no finiteness class, so we define one: a type is finite when some duplicate-free
list enumerates it. Every counting fact below comes from `Finite.length_le_of_subset`: a
duplicate-free list inside another list is no longer than it. -/

/-- A type is **finite** when some duplicate-free list lists every one of its elements. -/
class Finite (α : Type u) : Prop where
  out : ∃ l : List α, l.Nodup ∧ ∀ x, x ∈ l

namespace Finite

variable {α : Type u}

/-- A duplicate-free list contained in a second list is no longer than it. -/
theorem length_le_of_subset : ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) →
    l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: t, l₂, hnd, hsub => by
    classical
    have hnd' := List.nodup_cons.mp hnd
    have hx : x ∈ l₂ := hsub x (List.Mem.head _)
    have ht : ∀ y ∈ t, y ∈ l₂.erase x := fun y hy =>
      (List.mem_erase_of_ne (fun (h : y = x) => hnd'.1 (h ▸ hy))).mpr
        (hsub y (List.Mem.tail _ hy))
    have h₁ := length_le_of_subset hnd'.2 ht
    rw [List.length_erase_of_mem hx] at h₁
    have h₂ : 0 < l₂.length := by
      cases l₂ with
      | nil => cases hx
      | cons _ _ => exact Nat.succ_pos _
    show t.length + 1 ≤ l₂.length
    omega

/-- The number of elements of a finite type: the length of any duplicate-free enumeration
(`Finite.card_eq_length`). -/
noncomputable def card (α : Type u) [h : Finite α] : Nat :=
  (Classical.choose h.out).length

variable [h : Finite α]

/-- Every duplicate-free enumeration of `α` has length `card α`. -/
theorem card_eq_length {l : List α} (hnd : l.Nodup) (hall : ∀ x, x ∈ l) : card α = l.length :=
  have hspec := Classical.choose_spec h.out
  Nat.le_antisymm (length_le_of_subset hspec.1 fun x _ => hall x)
    (length_le_of_subset hnd fun x _ => hspec.2 x)

/-- A duplicate-free list has at most `card α` entries. -/
theorem length_le_card {l : List α} (hnd : l.Nodup) : l.length ≤ card α := by
  obtain ⟨l₀, hnd₀, hall₀⟩ := h.out
  rw [card_eq_length hnd₀ hall₀]
  exact length_le_of_subset hnd fun x _ => hall₀ x

/-- A duplicate-free list with `card α` entries lists every element of `α`. -/
theorem mem_of_length_eq_card {l : List α} (hnd : l.Nodup) (hl : l.length = card α) (x : α) :
    x ∈ l := by
  by_cases hx : x ∈ l
  · exact hx
  · have h₁ := length_le_card (List.nodup_cons.mpr ⟨hx, hnd⟩)
    simp only [List.length_cons] at h₁
    omega

/-- A list with fewer than `card α` entries misses some element of `α`. -/
theorem exists_notMem {l : List α} (hl : l.length < card α) : ∃ x, x ∉ l := by
  by_cases hx : ∃ x, x ∉ l
  · exact hx
  · obtain ⟨l₀, hnd₀, hall₀⟩ := h.out
    have h₁ := length_le_of_subset hnd₀ fun x _ =>
      Classical.byContradiction fun hxl => hx ⟨x, hxl⟩
    rw [← card_eq_length hnd₀ hall₀] at h₁
    omega

/-- **Six pairwise distinct elements of a six-element type exhaust it.** -/
theorem span_six (hM : card α = 6) {a b c d e f : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) (z : α) :
    z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f := by
  have hnd : [a, b, c, d, e, f].Nodup := by
    simp [List.nodup_cons, hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde,
      hdf, hef]
  have hz := mem_of_length_eq_card hnd ((rfl : [a, b, c, d, e, f].length = 6).trans hM.symm) z
  simpa using hz

end Finite

/-! ## Equation 677 and the division calculus -/

/-- **Equation 677**: $x = y \diamond (x \diamond ((y \diamond x) \diamond y))$. -/
def Equation677 (M : Type u) [Mul M] : Prop :=
  ∀ x y : M, x = y * (x * (y * x * y))

/-- **Equation 255 at the element `a`**: $((a \diamond a) \diamond a) \diamond a = a$, that is,
$R_a^3(a) = a$. -/
def Eq255At {M : Type u} [Mul M] (a : M) : Prop :=
  a * a * a * a = a

/-- `a` is **idempotent**: $a \diamond a = a$. (Mathlib's `IsIdempotentElem`.) -/
def IsIdempotentElem {M : Type u} [Mul M] (a : M) : Prop :=
  a * a = a

theorem IsIdempotentElem.eq {M : Type u} [Mul M] {a : M} (h : IsIdempotentElem a) :
    a * a = a :=
  h

/-- A `Mul` structure satisfying Equation 677. -/
class Magma677 (M : Type u) [Mul M] : Prop where
  protected out : Equation677 M

namespace Magma677

/-- **Left division**, $a / b := a \diamond ((b \diamond a) \diamond b)$. Equation 677 says
exactly that $b \diamond (a / b) = a$ (`Magma677.mul_div`); on a finite carrier $a / b$ is
therefore the unique solution of $L_b(x) = a$, that is $a / b = L_b^{-1}(a)$
(`Magma677.div_eq_iff_mul_eq`). The instance is scoped to the namespace `Magma677`. -/
scoped instance instDiv {M : Type u} [Mul M] [Magma677 M] : Div M :=
  ⟨fun a b => a * (b * a * b)⟩

section Mul

variable {M : Type u} [Mul M] [Magma677 M]

/-- Equation 677, oriented for rewriting:
$b \diamond (a \diamond ((b \diamond a) \diamond b)) = a$. -/
theorem eq677 (a b : M) : b * (a * (b * a * b)) = a :=
  (Magma677.out a b).symm

theorem div_def (a b : M) : a / b = a * (b * a * b) :=
  rfl

/-- $L_b(a / b) = a$: Equation 677 itself, so every $L_b$ is onto. -/
theorem mul_div (a b : M) : b * (a / b) = a :=
  eq677 a b

end Mul

section Finite

variable {M : Type u} [Mul M] [Magma677 M] [Finite M]

/-- **Left cancellation**: $L_a$ is injective. The map $x \mapsto x / a$ is injective, because
$L_a(x / a) = x$; so it lists $|M|$ distinct values and is onto. Every element is therefore some
$x / a$, and $L_a(x / a) = x$ recovers $x$. -/
theorem mul_left_cancel {a b c : M} (h : a * b = a * c) : b = c := by
  obtain ⟨l, hnd, hall⟩ := (Finite.out : ∃ l : List M, l.Nodup ∧ ∀ x, x ∈ l)
  have hnd' : (l.map (· / a)).Nodup := by
    refine List.Pairwise.map _ ?_ hnd
    intro x y hxy hq
    apply hxy
    calc x = a * (x / a) := (mul_div x a).symm
      _ = a * (y / a) := by rw [hq]
      _ = y := mul_div y a
  have hlen : (l.map (· / a)).length = Finite.card M := by
    rw [List.length_map, Finite.card_eq_length hnd hall]
  obtain ⟨x, -, hx⟩ := List.mem_map.mp (Finite.mem_of_length_eq_card hnd' hlen b)
  obtain ⟨y, -, hy⟩ := List.mem_map.mp (Finite.mem_of_length_eq_card hnd' hlen c)
  have hxy : x = y :=
    calc x = a * (x / a) := (mul_div x a).symm
      _ = a * b := by rw [hx]
      _ = a * c := h
      _ = a * (y / a) := by rw [hy]
      _ = y := mul_div y a
  rw [← hx, ← hy, hxy]

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
theorem eq_of_mul_eq_self_left {a b : M} (ha : IsIdempotentElem a) (h : a * b = a) : b = a :=
  mul_left_cancel (h.trans ha.symm)

/-- An idempotent has no left unit but itself: $a \diamond b = b$ forces $a = b$. -/
theorem eq_of_mul_eq_self_right {a b : M} (hb : IsIdempotentElem b) (h : a * b = b) :
    a = b := by
  have hc := eq_cube_of_mul_eq h
  rwa [hb, hb] at hc

/-- **A product equal to its backward step collapses**: $a \diamond b = a / b$ forces $a = b$,
provided $a / b$ is idempotent. -/
theorem eq_of_mul_eq_div {a b : M} (hu : IsIdempotentElem (a / b)) (h : a * b = a / b) :
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
theorem eq_of_mul_eq_div_div {a b : M} (hv : IsIdempotentElem (a / b / b))
    (h : a * b = a / b / b) : a = b := by
  have h2 : a / b / b / (a / b) = a / b / b := (mul_eq_div_div_div a b).symm.trans h
  have h4 : a / b = a / b / b := by
    have hc := eq_cube_of_mul_eq (div_eq_iff_mul_eq.mp h2)
    rwa [hv, hv] at hc
  have h5 : a = a / b :=
    calc a = b * (a / b) := (mul_div a b).symm
      _ = b * (a / b / b) := by rw [← h4]
      _ = a / b := mul_div (a / b) b
  have ha : IsIdempotentElem a := by
    have hchain : a = a / b / b := h5.trans h4
    rw [hchain]
    exact hv
  have h6 : b * a = a := (congrArg (b * ·) h5).trans (mul_div a b)
  have hc := eq_cube_of_mul_eq h6
  rw [ha, ha] at hc
  exact hc.symm

/-- $(a \diamond a) \diamond a = a$ forces $a$ to be idempotent. -/
theorem isIdempotentElem_of_cube_eq_self {a : M} (h : a * a * a = a) : IsIdempotentElem a :=
  (eq_cube_of_mul_eq h).trans h

/-- $a \diamond (a \diamond a) = a$ forces $a$ to be idempotent. -/
theorem isIdempotentElem_of_mul_sq {a : M} (h : a * (a * a) = a) : IsIdempotentElem a := by
  have h₁ : a / a = a * a := div_eq_iff_mul_eq.mpr h
  rw [div_def] at h₁
  exact isIdempotentElem_of_cube_eq_self (mul_left_cancel h₁)

/-- $(a \diamond a) \diamond (a \diamond a) = a$ forces $a$ to be idempotent. -/
theorem isIdempotentElem_of_sq_mul_sq {a : M} (h : a * a * (a * a) = a) :
    IsIdempotentElem a := by
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
    IsIdempotentElem a := by
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
    (h : a * (a * a) = a * a * a) : IsIdempotentElem a := by
  have h₁ : a / (a * a) = a := by
    have h' := div_div_eq_mul_mul (a := a * a) (b := a)
    rw [mul_div_cancel_left, h, h255] at h'
    exact h'
  exact isIdempotentElem_of_cube_eq_self (div_eq_iff_mul_eq.mp h₁)

/-- Under Equation 255 at $a$,
$a \diamond (a \diamond (a \diamond a)) = (a \diamond a) \diamond a$ forces $a$ to be
idempotent. -/
theorem isIdempotentElem_of_mul_mul_sq_eq_cube {a : M} (h255 : Eq255At a)
    (h : a * (a * (a * a)) = a * a * a) : IsIdempotentElem a := by
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

/-! ## The degree

For a fixed $a$, the points $L_a^n(a)$ run around the cycle of the permutation $L_a$ through
$a$; its length is the degree of $a$. Core Lean has neither `Function.minimalPeriod` nor
`Nat.find`, so the degree is a predicate `HasDeg a n` rather than a function, and its existence
(`exists_hasDeg`) is a pigeonhole argument followed by a least-witness argument. -/

section Orbit

variable {M : Type u} [Mul M]

/-- `leftApplyMul a b n` is $L_b^n(a) = b \diamond (b \diamond \cdots (b \diamond a))$. -/
def leftApplyMul (a b : M) : Nat → M
  | 0 => a
  | n + 1 => b * leftApplyMul a b n

/-- **The degree of `a` is `n`**: $n$ is the least positive exponent with $L_a^n(a) = a$. -/
def HasDeg (a : M) (n : Nat) : Prop :=
  0 < n ∧ leftApplyMul a a n = a ∧ ∀ k, 0 < k → k < n → leftApplyMul a a k ≠ a

/-- The first `n` points of the orbit, $[L_a^{n-1}(a), \dots, L_a(a), a]$. -/
def orbitList (a : M) : Nat → List M
  | 0 => []
  | n + 1 => leftApplyMul a a n :: orbitList a n

theorem length_orbitList (a : M) : ∀ n, (orbitList a n).length = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (length_orbitList a n)

theorem mem_orbitList {a x : M} : ∀ {n}, x ∈ orbitList a n → ∃ k, k < n ∧ leftApplyMul a a k = x
  | 0, h => nomatch h
  | n + 1, h => by
    rcases List.mem_cons.mp h with h | h
    · exact ⟨n, Nat.lt_succ_self n, h.symm⟩
    · obtain ⟨k, hk, hkx⟩ := mem_orbitList h
      exact ⟨k, Nat.lt_succ_of_lt hk, hkx⟩

theorem nodup_orbitList {a : M} : ∀ {n}, (∀ i j, i < n → j < n → i ≠ j →
    leftApplyMul a a i ≠ leftApplyMul a a j) → (orbitList a n).Nodup
  | 0, _ => List.Pairwise.nil
  | n + 1, h => List.nodup_cons.mpr
    ⟨fun hmem => by
      obtain ⟨k, hk, hkx⟩ := mem_orbitList hmem
      exact h n k (Nat.lt_succ_self n) (Nat.lt_succ_of_lt hk) (by omega) hkx.symm,
     nodup_orbitList fun i j hi hj => h i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj)⟩

end Orbit

/-- A least witness, by induction on a bound on some witness. -/
theorem exists_least {P : Nat → Prop} :
    ∀ n, (∃ k, k ≤ n ∧ P k) → ∃ m, P m ∧ ∀ k, k < m → ¬ P k := by
  intro n
  induction n with
  | zero =>
    rintro ⟨k, hk, hPk⟩
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨0, hPk, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    rintro ⟨k, hk, hPk⟩
    by_cases h : ∃ k, k ≤ n ∧ P k
    · exact ih h
    · have hkn : k = n + 1 := by
        by_cases hle : k ≤ n
        · exact absurd ⟨k, hle, hPk⟩ h
        · omega
      subst hkn
      exact ⟨n + 1, hPk, fun j hj hPj => h ⟨j, by omega, hPj⟩⟩

section Degree

variable {M : Type u} [Mul M] [Magma677 M] [Finite M]

/-- $L_a$ cancels along the orbit: $L_a^{i+k}(a) = L_a^{j+k}(a)$ forces
$L_a^i(a) = L_a^j(a)$. -/
theorem leftApplyMul_cancel (a : M) : ∀ k i j : Nat,
    leftApplyMul a a (i + k) = leftApplyMul a a (j + k) → leftApplyMul a a i = leftApplyMul a a j
  | 0, _, _, h => h
  | k + 1, i, j, h => leftApplyMul_cancel a k i j (mul_left_cancel h)

/-- A repetition $L_a^i(a) = L_a^j(a)$ with $i \le j$ is a return $L_a^{j-i}(a) = a$. -/
theorem leftApplyMul_sub_eq_self (a : M) {i j : Nat} (hij : i ≤ j)
    (h : leftApplyMul a a i = leftApplyMul a a j) : leftApplyMul a a (j - i) = a :=
  (leftApplyMul_cancel a i 0 (j - i) (by rw [Nat.zero_add, Nat.sub_add_cancel hij]; exact h)).symm

/-- **One turn of the orbit visits distinct points**: if $a$ has degree $n$, the points
$L_a^k(a)$ for $k < n$ are pairwise distinct. -/
theorem HasDeg.ne {a : M} {n : Nat} (h : HasDeg a n) {i j : Nat} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) : leftApplyMul a a i ≠ leftApplyMul a a j := by
  intro heq
  rcases (by omega : i < j ∨ j < i) with hlt | hlt
  · exact h.2.2 (j - i) (by omega) (by omega)
      (leftApplyMul_sub_eq_self a (Nat.le_of_lt hlt) heq)
  · exact h.2.2 (i - j) (by omega) (by omega)
      (leftApplyMul_sub_eq_self a (Nat.le_of_lt hlt) heq.symm)

/-- **Every element has a degree, at most $|M|$.** Among the $|M| + 1$ points
$a, L_a(a), \dots, L_a^{|M|}(a)$ two coincide, which by cancellation is a return to $a$; the
degree is the least return time. -/
theorem exists_hasDeg (a : M) : ∃ n, n ≤ Finite.card M ∧ HasDeg a n := by
  have hret : ∃ k, (0 < k ∧ leftApplyMul a a k = a) ∧ k ≤ Finite.card M := by
    by_cases h : ∃ k, (0 < k ∧ leftApplyMul a a k = a) ∧ k ≤ Finite.card M
    · exact h
    · have hdist : ∀ i j, i < Finite.card M + 1 → j < Finite.card M + 1 → i ≠ j →
          leftApplyMul a a i ≠ leftApplyMul a a j := by
        intro i j hi hj hij heq
        rcases (by omega : i < j ∨ j < i) with hlt | hlt
        · exact h ⟨j - i, ⟨by omega, leftApplyMul_sub_eq_self a (Nat.le_of_lt hlt) heq⟩,
            by omega⟩
        · exact h ⟨i - j, ⟨by omega, leftApplyMul_sub_eq_self a (Nat.le_of_lt hlt) heq.symm⟩,
            by omega⟩
      have hle := Finite.length_le_card (nodup_orbitList hdist)
      rw [length_orbitList] at hle
      omega
  obtain ⟨k, hk, hkM⟩ := hret
  obtain ⟨m, hPm, hmin⟩ :=
    exists_least (P := fun k => 0 < k ∧ leftApplyMul a a k = a) k ⟨k, Nat.le_refl k, hk⟩
  have hmk : m ≤ k := by
    by_cases hlt : k < m
    · exact absurd hk (hmin k hlt)
    · omega
  exact ⟨m, Nat.le_trans hmk hkM, hPm.1, hPm.2, fun j hj0 hjm hj => hmin j hjm ⟨hj0, hj⟩⟩

/-- **No element has degree $2$**: $a \diamond (a \diamond a) = a$ forces idempotence, which is
a return at time $1$. -/
theorem not_hasDeg_two (a : M) : ¬ HasDeg a 2 := fun h =>
  h.2.2 1 (by decide) (by decide) (isIdempotentElem_of_mul_sq (a := a) h.2.1)

/-- **No element has degree $3$.** -/
theorem not_hasDeg_three (a : M) : ¬ HasDeg a 3 := fun h =>
  h.2.2 1 (by decide) (by decide) (isIdempotentElem_of_mul_mul_sq (a := a) h.2.1)

/-- **An element satisfying Equation 255 does not have degree $4$**: $L_a^4(a) = a$ says
$a \diamond (a \diamond a) = (a \diamond a) \diamond a$. -/
theorem not_hasDeg_four_of_eq255At {a : M} (h255 : Eq255At a) : ¬ HasDeg a 4 := fun h => by
  have h₁ : a / a = a * (a * (a * a)) := div_eq_iff_mul_eq.mpr h.2.1
  rw [div_def] at h₁
  exact h.2.2 1 (by decide) (by decide)
    (isIdempotentElem_of_mul_sq_eq_sq_mul h255 (mul_left_cancel h₁).symm)

/-- **An element satisfying Equation 255 does not have degree $5$**: $L_a^5(a) = a$ says
$a \diamond (a \diamond (a \diamond a)) = (a \diamond a) \diamond a$. -/
theorem not_hasDeg_five_of_eq255At {a : M} (h255 : Eq255At a) : ¬ HasDeg a 5 := fun h => by
  have h₁ : a / a = a * (a * (a * (a * a))) := div_eq_iff_mul_eq.mpr h.2.1
  rw [div_def] at h₁
  exact h.2.2 1 (by decide) (by decide)
    (isIdempotentElem_of_mul_mul_sq_eq_cube h255 (mul_left_cancel h₁).symm)

end Degree

/-! ## Order six -/

section OrderSix

variable {M : Type u} [Mul M] [Magma677 M] [Finite M]

/-- **A six-element magma has no element of degree $6$.**

An element $a$ of degree $6$ would have its orbit $a, b, c, d, e, f$ under $L_a$ exhaust the
carrier, with $e = (a \diamond a) \diamond a$ two steps and $f = a / a$ one step before $a$.
Three cells are known at once: the row of $a$ is the six-cycle, $b \diamond a = e$ is the
definition of the cube, and $f \diamond b = e$ is `div_self_mul_sq`. The rest is a case analysis,
split at the top on whether Equation 255 holds at $a$, that is, on the cell $e \diamond a$.

* If $e \diamond a = a$, Equation 677 at the pairs $(d, a)$ and $(c, a)$ forces
  $d \diamond a = c$ and $c \diamond c = b$, and the analysis splits on $b \diamond b$ and
  then on further cells of the row of $b$.
* Otherwise no element is a left unit for $a$, since a left unit would be the cube $e$
  (`eq_cube_of_mul_eq`); the value $a$ is barred from the column of $a$, and the analysis
  splits first on $f \diamond a$ and then on cells of the rows of $d$ and $e$. -/
theorem not_hasDeg_six_of_card_eq_six (hM : Finite.card M = 6) (a : M) : ¬ HasDeg a 6 := by
  intro hdeg
  -- one turn of the orbit, named
  obtain ⟨b, hb⟩ : ∃ b, b = a * a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = a * c := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = a * d := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = a * e := ⟨_, rfl⟩
  -- the turn closes up: $L_a(f) = a$
  have haf : a * f = a := by
    rw [hf, he, hd, hc, hb]
    exact hdeg.2.1
  -- the two backward names: $f = a / a$ and $e = (a \diamond a) \diamond a$
  have hFdiv : f = a / a := (div_eq_iff_mul_eq.mpr haf).symm
  have hEcube : e = a * a * a :=
    (div_eq_iff_mul_eq.mpr (hf.symm.trans hFdiv)).symm.trans div_div_eq_mul_mul
  -- the two seeded cells: the cube is $b \diamond a$, and `div_self_mul_sq`
  have hba : b * a = e := by rw [hEcube, hb]
  have hfb : f * b = e := by rw [hFdiv, hb, hEcube]; exact div_self_mul_sq a
  -- distinctness of one turn
  have hNE : ∀ m n : Nat, m < 6 → n < 6 → m ≠ n →
      leftApplyMul a a m ≠ leftApplyMul a a n := fun _ _ hm hn hmn => hdeg.ne hm hn hmn
  have hab : a ≠ b := by rw [hb]; exact hNE 0 1 (by omega) (by omega) (by omega)
  have hac : a ≠ c := by rw [hc, hb]; exact hNE 0 2 (by omega) (by omega) (by omega)
  have had : a ≠ d := by rw [hd, hc, hb]; exact hNE 0 3 (by omega) (by omega) (by omega)
  have hae : a ≠ e := by rw [he, hd, hc, hb]; exact hNE 0 4 (by omega) (by omega) (by omega)
  have haf' : a ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 0 5 (by omega) (by omega) (by omega)
  have hbc : b ≠ c := by rw [hc, hb]; exact hNE 1 2 (by omega) (by omega) (by omega)
  have hbd : b ≠ d := by rw [hd, hc, hb]; exact hNE 1 3 (by omega) (by omega) (by omega)
  have hbe : b ≠ e := by rw [he, hd, hc, hb]; exact hNE 1 4 (by omega) (by omega) (by omega)
  have hbf : b ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 1 5 (by omega) (by omega) (by omega)
  have hcd : c ≠ d := by rw [hd, hc, hb]; exact hNE 2 3 (by omega) (by omega) (by omega)
  have hce : c ≠ e := by rw [he, hd, hc, hb]; exact hNE 2 4 (by omega) (by omega) (by omega)
  have hcf : c ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 2 5 (by omega) (by omega) (by omega)
  have hde : d ≠ e := by rw [he, hd, hc, hb]; exact hNE 3 4 (by omega) (by omega) (by omega)
  have hdf : d ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 3 5 (by omega) (by omega) (by omega)
  have hef : e ≠ f := by
    rw [hf, he, hd, hc, hb]; exact hNE 4 5 (by omega) (by omega) (by omega)
  -- one turn of the orbit is the whole carrier
  have hspan : ∀ z : M, z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f :=
    Finite.span_six hM hab hac had hae haf' hbc hbd hbe hbf hcd hce hcf hde hdf hef
  by_cases h255c : e * a = a
  · -- Equation 255 holds at $a$
    have hv1 : d * a = c :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
        ((congrArg (· * a) he.symm).trans h255c))).symm.trans
        (eq677 d a)).trans hd.symm.symm)
    have hv2 : c * c = b :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
        ((congrArg (· * a) hd.symm).trans hv1))).symm.trans
        (eq677 c a)).trans hc.symm.symm)
    rcases hspan (b * b) with hcs3 | hcs3 | hcs3 | hcs3 | hcs3 | hcs3
    · -- $b \diamond b = a$
      have e : a * a * (a * a) = a := by rw [hb.symm]; exact hcs3
      exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
    · -- $b \diamond b = b$
      rcases hspan (b * e) with hcs4 | hcs4 | hcs4 | hcs4 | hcs4 | hcs4
      · -- $b \diamond e = a$
        have hv5 : c * a = e :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
            (eq677 b a)).trans hb.symm.symm)).trans hcs4.symm)
        have hv6 : e * b = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
            (eq677 a b)).trans hcs4.symm)).trans he.symm.symm)
        have hv7 : e * c = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs4).trans hc.symm))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv7.trans h255c.symm)) (hac.symm)
      · -- $b \diamond e = b$
        exact absurd (mul_left_cancel (hcs4.trans hcs3.symm)) (hbe.symm)
      · -- $b \diamond e = c$
        have hv8 : c * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs4))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv9 : b * d = c :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv8).trans hd.symm))).symm.trans
            (eq677 b c)).trans hv2.symm)
        exact absurd (mul_left_cancel (hv9.trans hcs4.symm)) hde
      · -- $b \diamond e = d$
        have hv10 : d * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs4))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv11 : c * d = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
            (congrArg (a * ·) (congrArg (· * d) hv1))).symm.trans
            (eq677 a d)).trans hv10.symm)).trans hb.symm.symm)
        have hv12 : d * d = b :=
          (congrArg (d * ·) ((congrArg (b * ·) ((congrArg (· * d) hv10).trans
            he.symm)).trans hcs4)).symm.trans (eq677 b d)
        have hv13 : c * b = d :=
          (congrArg (c * ·) ((congrArg (d * ·) ((congrArg (· * c) hv11).trans
            hd.symm)).trans hv12)).symm.trans (eq677 d c)
        rcases hspan (b * f) with hcs14 | hcs14 | hcs14 | hcs14 | hcs14 | hcs14
        · -- $b \diamond f = a$
          have hv15 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hcs14.symm)
          have hv16 : e * b = e :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
              (eq677 a b)).trans hcs14.symm)).trans hf.symm.symm)
          have hv17 : f * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hv15))).symm.trans
              (eq677 a c)).trans hv11.symm)).trans hd.symm.symm)
          have hv18 : b * c = f := by
            have e := eq_cube_of_mul_eq hv17
            rw [hv2] at e
            exact e.symm
          have hv19 : b * d = c := by
            rcases hspan (b * d) with hz | hz | hz | hz | hz | hz
            · exact absurd (mul_left_cancel (hz.trans hcs14.symm)) hdf
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hbd.symm)
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hcs4.symm)) hde
            · exact absurd (mul_left_cancel (hz.trans hba.symm)) (had.symm)
            · exact absurd (mul_left_cancel (hz.trans hv18.symm)) (hcd.symm)
          have hv20 : c * e = d :=
            mul_left_cancel (((congrArg (b * ·) (congrArg (c * ·)
              ((congrArg (· * b) hv18).trans hfb))).symm.trans
              (eq677 c b)).trans hv19.symm)
          exact absurd (mul_left_cancel (hv20.trans hv13.symm)) (hbe.symm)
        · -- $b \diamond f = b$
          exact absurd (mul_left_cancel (hcs14.trans hcs3.symm)) (hbf.symm)
        · -- $b \diamond f = c$
          have hv21 : d * c = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (b * ·) (congrArg (· * c) hv13))).symm.trans
              (eq677 b c)).trans hv2.symm)).trans hcs14.symm)
          have hv22 : f * d = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (c * ·) (congrArg (· * d) hv21))).symm.trans
              (eq677 c d)).trans hv1.symm)).trans hv11.symm)
          have hv23 : b * d = f := by
            have e := eq_cube_of_mul_eq hv22
            rw [hv12] at e
            exact e.symm
          have hv24 : b * c = a := by
            rcases hspan (b * c) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hbc.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs14.symm)) hcf
            · exact absurd (mul_left_cancel (hz.trans hcs4.symm)) hce
            · exact absurd (mul_left_cancel (hz.trans hba.symm)) (hac.symm)
            · exact absurd (mul_left_cancel (hz.trans hv23.symm)) hcd
          have hv25 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv24.symm)
          have hv26 : e * b = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
              (eq677 a b)).trans hv24.symm)).trans hc.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs3).trans (eq_cube_of_mul_eq hv26).symm) hbe
        · -- $b \diamond f = d$
          exact absurd (mul_left_cancel (hcs14.trans hcs4.symm)) (hef.symm)
        · -- $b \diamond f = e$
          exact absurd (mul_left_cancel (hcs14.trans hba.symm)) (haf'.symm)
        · -- $b \diamond f = f$
          have hv27 : f * e = f := by
            have e := mul_mul_eq_self_of_mul_eq hcs14
            rw [hfb] at e
            exact e
          rcases hspan (b * c) with hcs28 | hcs28 | hcs28 | hcs28 | hcs28 | hcs28
          · -- $b \diamond c = a$
            have hv29 : c * a = c :=
              mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
                (eq677 b a)).trans hb.symm.symm)).trans hcs28.symm)
            have hv30 : e * b = b :=
              mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
                (eq677 a b)).trans hcs28.symm)).trans hc.symm.symm)
            exact absurd ((eq_cube_of_mul_eq hcs3).trans (eq_cube_of_mul_eq hv30).symm) hbe
          · -- $b \diamond c = b$
            exact absurd (mul_left_cancel (hcs28.trans hcs3.symm)) (hbc.symm)
          · -- $b \diamond c = c$
            have e : c * c * c = c := by rw [hv2]; exact hcs28
            exact absurd ((isIdempotentElem_of_cube_eq_self e).eq.symm.trans hv2) (hbc.symm)
          · -- $b \diamond c = d$
            exact absurd (mul_left_cancel (hcs28.trans hcs4.symm)) hce
          · -- $b \diamond c = e$
            exact absurd (mul_left_cancel (hcs28.trans hba.symm)) (hac.symm)
          · -- $b \diamond c = f$
            exact absurd (mul_left_cancel (hcs28.trans hcs14.symm)) hcf
      · -- $b \diamond e = e$
        exact absurd (mul_left_cancel (hcs4.trans hba.symm)) (hae.symm)
      · -- $b \diamond e = f$
        have hv31 : e * e = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs4).trans hfb))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv31.trans h255c.symm)) (hae.symm)
    · -- $b \diamond b = c$
      have e : b * b * (b * b) = b := by rw [hcs3]; exact hv2
      exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hcs3) hbc
    · -- $b \diamond b = d$
      rcases hspan (b * e) with hcs32 | hcs32 | hcs32 | hcs32 | hcs32 | hcs32
      · -- $b \diamond e = a$
        have hv33 : c * a = e :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
            (eq677 b a)).trans hb.symm.symm)).trans hcs32.symm)
        have hv34 : e * b = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
            (eq677 a b)).trans hcs32.symm)).trans he.symm.symm)
        have hv35 : e * c = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs32).trans hc.symm))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv35.trans h255c.symm)) (hac.symm)
      · -- $b \diamond e = b$
        have hv36 : d * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (b * ·) (congrArg (· * b) hcs3))).symm.trans
            (eq677 b b)).trans hcs32.symm)).trans hba.symm)
        have hv37 : e * d = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs32).trans hcs3))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv37.trans h255c.symm)) (had.symm)
      · -- $b \diamond e = c$
        have hv38 : c * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs32))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv39 : b * d = c :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv38).trans hd.symm))).symm.trans
            (eq677 b c)).trans hv2.symm)
        exact absurd (mul_left_cancel (hv39.trans hcs32.symm)) hde
      · -- $b \diamond e = d$
        exact absurd (mul_left_cancel (hcs32.trans hcs3.symm)) (hbe.symm)
      · -- $b \diamond e = e$
        exact absurd (mul_left_cancel (hcs32.trans hba.symm)) (hae.symm)
      · -- $b \diamond e = f$
        have hv40 : e * e = a :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
            ((congrArg (· * b) hcs32).trans hfb))).symm.trans
            (eq677 e b)).trans hba.symm)
        exact absurd (mul_left_cancel (hv40.trans h255c.symm)) (hae.symm)
    · -- $b \diamond b = e$
      exact absurd (mul_left_cancel (hcs3.trans hba.symm)) (hab.symm)
    · -- $b \diamond b = f$
      rcases hspan (b * e) with hcs41 | hcs41 | hcs41 | hcs41 | hcs41 | hcs41
      · -- $b \diamond e = a$
        have hv42 : c * a = e :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
            (eq677 b a)).trans hb.symm.symm)).trans hcs41.symm)
        have hv43 : e * b = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
            (eq677 a b)).trans hcs41.symm)).trans he.symm.symm)
        have hv44 : b * a = b :=
          (congrArg (b * ·) ((congrArg (b * ·) ((congrArg (· * b) hcs3).trans
            hfb)).trans hcs41)).symm.trans (eq677 b b)
        exact absurd (hv44.symm.trans hba) hbe
      · -- $b \diamond e = b$
        have hv45 : b * b = b :=
          (congrArg (b * ·) ((congrArg (b * ·) ((congrArg (· * b) hcs3).trans
            hfb)).trans hcs41)).symm.trans (eq677 b b)
        exact absurd (hv45.symm.trans hcs3) hbf
      · -- $b \diamond e = c$
        have hv46 : b * c = b :=
          (congrArg (b * ·) ((congrArg (b * ·) ((congrArg (· * b) hcs3).trans
            hfb)).trans hcs41)).symm.trans (eq677 b b)
        have hv47 : c * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs41))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv48 : c * f = e :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (c * ·)
            ((congrArg (· * b) hv46).trans hcs3))).symm.trans
            (eq677 c b)).trans hcs41.symm)
        have hv49 : b * d = c :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv47).trans hd.symm))).symm.trans
            (eq677 b c)).trans hv2.symm)
        exact absurd (mul_left_cancel (hv49.trans hcs41.symm)) hde
      · -- $b \diamond e = d$
        have hv50 : b * d = b :=
          (congrArg (b * ·) ((congrArg (b * ·) ((congrArg (· * b) hcs3).trans
            hfb)).trans hcs41)).symm.trans (eq677 b b)
        have hv51 : d * b = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
            (congrArg (e * ·) (congrArg (· * b) hcs41))).symm.trans
            (eq677 e b)).trans hba.symm)).trans h255c.symm)
        have hv52 : d * f = e :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
            ((congrArg (· * b) hv50).trans hcs3))).symm.trans
            (eq677 d b)).trans hcs41.symm)
        have hv53 : c * d = a :=
          mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
            (congrArg (a * ·) (congrArg (· * d) hv1))).symm.trans
            (eq677 a d)).trans hv51.symm)).trans hb.symm.symm)
        have hv54 : d * d = b :=
          (congrArg (d * ·) ((congrArg (b * ·) ((congrArg (· * d) hv51).trans
            he.symm)).trans hcs41)).symm.trans (eq677 b d)
        have hv55 : d * a = d :=
          (congrArg (d * ·) ((congrArg (d * ·) ((congrArg (· * d) hv54).trans
            hv50)).trans hv51)).symm.trans (eq677 d d)
        exact absurd (hv55.symm.trans hv1) (hcd.symm)
      · -- $b \diamond e = e$
        exact absurd (mul_left_cancel (hcs41.trans hba.symm)) (hae.symm)
      · -- $b \diamond e = f$
        exact absurd (mul_left_cancel (hcs41.trans hcs3.symm)) (hbe.symm)
  · -- no element is a left unit for $a$
    have hno : ∀ x : M, x * a ≠ a := by
      intro x hx
      have h' := eq_cube_of_mul_eq hx
      rw [← hb, hba] at h'
      exact h255c (h' ▸ hx)
    rcases hspan (f * a) with hcs1 | hcs1 | hcs1 | hcs1 | hcs1 | hcs1
    · -- $f \diamond a = a$
      exact absurd hcs1 (hno _)
    · -- $f \diamond a = b$
      have hv2 : e * b = d :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
          ((congrArg (· * a) hf.symm).trans hcs1))).symm.trans
          (eq677 e a)).trans he.symm.symm)
      have hv3 : b * e = a :=
        (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
          hv2)).trans he.symm)).symm.trans (eq677 a b)
      have hv4 : e * c = a :=
        mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
          ((congrArg (· * b) hv3).trans hc.symm))).symm.trans
          (eq677 e b)).trans hba.symm)
      have hv5 : e * f = e :=
        mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
          (congrArg (b * ·) (congrArg (· * f) hfb))).symm.trans
          (eq677 b f)).trans hcs1.symm)).trans hv3.symm)
      have hv6 : c * a = e :=
        mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
          (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
          (eq677 b a)).trans hb.symm.symm)).trans hv3.symm)
      have hv7 : c * b = a :=
        (congrArg (c * ·) ((congrArg (a * ·) ((congrArg (· * c) hv6).trans
          hv4)).trans hb.symm)).symm.trans (eq677 a c)
      rcases hspan (e * a) with hcs8 | hcs8 | hcs8 | hcs8 | hcs8 | hcs8
      · -- $e \diamond a = a$
        exact absurd (mul_left_cancel (hcs8.trans hv4.symm)) hac
      · -- $e \diamond a = b$
        have hv9 : d * b = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs8))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv10 : e * b = a :=
          (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs8).trans
            hv3)).trans hb.symm)).symm.trans (eq677 a e)
        exact absurd (hv10.symm.trans hv2) had
      · -- $e \diamond a = c$
        have hv11 : d * c = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs8))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv12 : c * e = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
            (congrArg (a * ·) (congrArg (· * e) hcs8))).symm.trans
            (eq677 a e)).trans hv4.symm)).trans hc.symm.symm)
        have hv13 : c * f = a :=
          mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
            ((congrArg (· * e) hv4).trans hf.symm))).symm.trans
            (eq677 c e)).trans hcs8.symm)
        exact absurd (mul_left_cancel (hv13.trans hv7.symm)) (hbf.symm)
      · -- $e \diamond a = d$
        exact absurd (mul_left_cancel (hcs8.trans hv2.symm)) hab
      · -- $e \diamond a = e$
        exact absurd (mul_left_cancel (hcs8.trans hv5.symm)) haf'
      · -- $e \diamond a = f$
        have hv14 : d * f = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs8))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv15 : f * e = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
            (congrArg (a * ·) (congrArg (· * e) hcs8))).symm.trans
            (eq677 a e)).trans hv4.symm)).trans hc.symm.symm)
        exact absurd (mul_left_cancel (hv15.trans hcs1.symm)) (hae.symm)
    · -- $f \diamond a = c$
      have hv16 : e * c = d :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
          ((congrArg (· * a) hf.symm).trans hcs1))).symm.trans
          (eq677 e a)).trans he.symm.symm)
      rcases hspan (e * a) with hcs17 | hcs17 | hcs17 | hcs17 | hcs17 | hcs17
      · -- $e \diamond a = a$
        exact absurd hcs17 (hno _)
      · -- $e \diamond a = b$
        have hv18 : d * b = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs17))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs19 | hcs19 | hcs19 | hcs19 | hcs19 | hcs19
        · -- $e \diamond b = a$
          have hv20 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs19)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv20
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          exact absurd (mul_left_cancel (hcs19.trans hcs17.symm)) (hab.symm)
        · -- $e \diamond b = c$
          have e1 : e * a = a * a := hcs17.trans hb.symm.symm
          have e2 : e * (a * a) = a * (a * a) := by
            rw [hb.symm]
            exact hcs19.trans hc.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs19.trans hv16.symm)) hbc
        · -- $e \diamond b = e$
          have hv21 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs19)).trans hf.symm)).symm.trans (eq677 a b)
          have hv22 : e * e = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (b * ·) (congrArg (· * e) hcs19))).symm.trans
              (eq677 b e)).trans hcs17.symm)).trans hv21.symm)
          have hv23 : f * e = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (e * ·) (congrArg (· * e) hv22))).symm.trans
              (eq677 e e)).trans hcs19.symm)).trans hcs17.symm)
          have hv24 : c * f = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
              (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
              (eq677 a f)).trans hv23.symm)).trans he.symm.symm)
          have hv25 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv21.symm)
          have hv26 : d * c = e :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (f * ·) (congrArg (· * c) hv24))).symm.trans
              (eq677 f c)).trans hv25.symm)).trans hv23.symm)
          rcases hspan (e * f) with hcs27 | hcs27 | hcs27 | hcs27 | hcs27 | hcs27
          · -- $e \diamond f = a$
            have e1 : e * e = a * e := hv22.trans hf.symm.symm
            have e2 : e * (a * e) = a * (a * e) := by
              rw [hf.symm]
              exact hcs27.trans haf.symm
            exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
          · -- $e \diamond f = b$
            exact absurd (mul_left_cancel (hcs27.trans hcs17.symm)) (haf'.symm)
          · -- $e \diamond f = c$
            have hv28 : c * e = b :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (f * ·) (congrArg (· * e) hcs27))).symm.trans
                (eq677 f e)).trans hv22.symm)).trans hfb.symm)
            have hv29 : d * e = a :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (c * ·) (congrArg (· * e) hv16))).symm.trans
                (eq677 c e)).trans hcs27.symm)).trans hv25.symm)
            have hv30 : d * f = e :=
              (congrArg (d * ·) ((congrArg (e * ·) ((congrArg (· * d) hv29).trans
                he.symm)).trans hv22)).symm.trans (eq677 e d)
            exact absurd (mul_left_cancel (hv30.trans hv26.symm)) (hcf.symm)
          · -- $e \diamond f = d$
            exact absurd (mul_left_cancel (hcs27.trans hv16.symm)) (hcf.symm)
          · -- $e \diamond f = e$
            exact absurd (mul_left_cancel (hcs27.trans hcs19.symm)) (hbf.symm)
          · -- $e \diamond f = f$
            exact absurd (mul_left_cancel (hcs27.trans hv22.symm)) (hef.symm)
        · -- $e \diamond b = f$
          have hv31 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs19)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv31.symm.trans hba) hae
      · -- $e \diamond a = c$
        have hv32 : d * c = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs17))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs33 | hcs33 | hcs33 | hcs33 | hcs33 | hcs33
        · -- $e \diamond b = a$
          have hv34 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs33)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv34
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv35 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs33)).trans hc.symm)).symm.trans (eq677 a b)
          have hv36 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv35.symm)
          have hv37 : c * d = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (c * ·) (congrArg (· * d) hv32))).symm.trans
              (eq677 c d)).trans hv32.symm)).trans hv36.symm)
          have hv38 : d * e = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (c * ·) (congrArg (· * e) hv16))).symm.trans
              (eq677 c e)).trans hcs17.symm)).trans hv37.symm)
          have hv39 : c * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hv36))).symm.trans
              (eq677 a c)).trans hv37.symm)).trans hd.symm.symm)
          exact absurd (mul_left_cancel (hv39.trans hv36.symm)) (hac.symm)
        · -- $e \diamond b = c$
          exact absurd (mul_left_cancel (hcs33.trans hcs17.symm)) (hab.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs33.trans hv16.symm)) hbc
        · -- $e \diamond b = e$
          have hv40 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs33)).trans hf.symm)).symm.trans (eq677 a b)
          have hv41 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv40.symm)
          rcases hspan (e * e) with hcs42 | hcs42 | hcs42 | hcs42 | hcs42 | hcs42
          · -- $e \diamond e = a$
            have hv43 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                (eq677 a e)).trans hcs42.symm)).trans he.symm.symm)
            have hv44 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs33).trans
                hcs42)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv44.symm.trans hcs42) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs42]; exact hcs33
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs42) (hbe.symm)
          · -- $e \diamond e = c$
            exact absurd (mul_left_cancel (hcs42.trans hcs17.symm)) (hae.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs42.trans hv16.symm)) (hce.symm)
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs42.trans hcs33.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            have hv45 : e * a = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs33).trans
                hcs42)).trans hv40)).symm.trans (eq677 b e)
            exact absurd (hv45.symm.trans hcs17) hbc
        · -- $e \diamond b = f$
          have hv46 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs33)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv46.symm.trans hba) hae
      · -- $e \diamond a = d$
        exact absurd (mul_left_cancel (hcs17.trans hv16.symm)) hac
      · -- $e \diamond a = e$
        have hv47 : d * e = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs17))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs48 | hcs48 | hcs48 | hcs48 | hcs48 | hcs48
        · -- $e \diamond b = a$
          have hv49 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs48)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv49
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv50 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs48)).trans hc.symm)).symm.trans (eq677 a b)
          have hv51 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv50.symm)
          rcases hspan (e * e) with hcs52 | hcs52 | hcs52 | hcs52 | hcs52 | hcs52
          · -- $e \diamond e = a$
            have e : e * (e * e) = e := by rw [hcs52]; exact hcs17
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs52) (hae.symm)
          · -- $e \diamond e = b$
            exact absurd (mul_left_cancel (hcs52.trans hcs48.symm)) (hbe.symm)
          · -- $e \diamond e = c$
            have hv53 : e * d = a :=
              (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs17).trans
                hcs52)).trans hd.symm)).symm.trans (eq677 a e)
            have hv54 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (e * ·) (congrArg (· * e) hcs52))).symm.trans
                (eq677 e e)).trans hcs17.symm)).trans hv53.symm)
            have hv55 : c * c = e :=
              mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                ((congrArg (· * e) hv16).trans hv47))).symm.trans
                (eq677 c e)).trans hcs52.symm)
            have e : e * e * (e * e) = e := by rw [hcs52]; exact hv55
            exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hcs52) (hce.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs52.trans hv16.symm)) (hce.symm)
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs52.trans hcs17.symm)) (hae.symm)
          · -- $e \diamond e = f$
            have hv56 : e * a = a :=
              (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs17).trans
                hcs52)).trans haf)).symm.trans (eq677 a e)
            exact absurd (hv56.symm.trans hcs17) hae
        · -- $e \diamond b = c$
          have e1 : e * b = a * b := hcs48.trans hc.symm.symm
          have e2 : e * (a * b) = a * (a * b) := by
            rw [hc.symm]
            exact hv16.trans hd.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs48.trans hv16.symm)) hbc
        · -- $e \diamond b = e$
          exact absurd (mul_left_cancel (hcs48.trans hcs17.symm)) (hab.symm)
        · -- $e \diamond b = f$
          have hv57 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs48)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv57.symm.trans hba) hae
      · -- $e \diamond a = f$
        have hv58 : d * f = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs17))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs59 | hcs59 | hcs59 | hcs59 | hcs59 | hcs59
        · -- $e \diamond b = a$
          have hv60 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs59)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv60
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv61 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs59)).trans hc.symm)).symm.trans (eq677 a b)
          have hv62 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv61.symm)
          rcases hspan (e * e) with hcs63 | hcs63 | hcs63 | hcs63 | hcs63 | hcs63
          · -- $e \diamond e = a$
            have hv64 : f * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                (eq677 a e)).trans hcs63.symm)).trans he.symm.symm)
            have hv65 : f * d = e :=
              (congrArg (f * ·) ((congrArg (e * ·) ((congrArg (· * f) hv64).trans
                hv58)).trans hv16)).symm.trans (eq677 e f)
            exact absurd (mul_left_cancel (hv65.trans hfb.symm)) (hbd.symm)
          · -- $e \diamond e = b$
            exact absurd (mul_left_cancel (hcs63.trans hcs59.symm)) (hbe.symm)
          · -- $e \diamond e = c$
            rcases hspan (e * f) with hcs66 | hcs66 | hcs66 | hcs66 | hcs66 | hcs66
            · -- $e \diamond f = a$
              have hv67 : f * e = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                  (eq677 a e)).trans hcs66.symm)).trans hf.symm.symm)
              exact absurd (mul_left_cancel (hv67.trans hfb.symm)) (hbe.symm)
            · -- $e \diamond f = b$
              exact absurd (mul_left_cancel (hcs66.trans hcs59.symm)) (hbf.symm)
            · -- $e \diamond f = c$
              exact absurd (mul_left_cancel (hcs66.trans hcs63.symm)) (hef.symm)
            · -- $e \diamond f = d$
              exact absurd (mul_left_cancel (hcs66.trans hv16.symm)) (hcf.symm)
            · -- $e \diamond f = e$
              have hv68 : c * e = a :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (e * ·) (congrArg (· * e) hcs63))).symm.trans
                  (eq677 e e)).trans hcs66.symm)).trans hcs17.symm)
              have hv69 : f * c = a :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (f * ·)
                  ((congrArg (· * e) hcs66).trans hcs63))).symm.trans
                  (eq677 f e)).trans hcs17.symm)
              have hv70 : c * f = b :=
                mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
                  (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
                  (eq677 a f)).trans hv69.symm)).trans hc.symm.symm)
              have hv71 : f * c = c :=
                (congrArg (f * ·) ((congrArg (c * ·) ((congrArg (· * f) hv69).trans
                  haf)).trans hv62)).symm.trans (eq677 c f)
              exact absurd (hv71.symm.trans hv69) (hac.symm)
            · -- $e \diamond f = f$
              exact absurd (mul_left_cancel (hcs66.trans hcs17.symm)) (haf'.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs63.trans hv16.symm)) (hce.symm)
          · -- $e \diamond e = e$
            rcases hspan (e * f) with hcs72 | hcs72 | hcs72 | hcs72 | hcs72 | hcs72
            · -- $e \diamond f = a$
              have hv73 : f * e = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                  (eq677 a e)).trans hcs72.symm)).trans hf.symm.symm)
              exact absurd (mul_left_cancel (hv73.trans hfb.symm)) (hbe.symm)
            · -- $e \diamond f = b$
              exact absurd (mul_left_cancel (hcs72.trans hcs59.symm)) (hbf.symm)
            · -- $e \diamond f = c$
              have hv74 : f * a = b :=
                (congrArg (f * ·) ((congrArg (b * ·) ((congrArg (· * f) hfb).trans
                  hcs72)).trans hv61)).symm.trans (eq677 b f)
              exact absurd (hv74.symm.trans hcs1) hbc
            · -- $e \diamond f = d$
              exact absurd (mul_left_cancel (hcs72.trans hv16.symm)) (hcf.symm)
            · -- $e \diamond f = e$
              exact absurd (mul_left_cancel (hcs72.trans hcs63.symm)) (hef.symm)
            · -- $e \diamond f = f$
              exact absurd (mul_left_cancel (hcs72.trans hcs17.symm)) (haf'.symm)
          · -- $e \diamond e = f$
            exact absurd (mul_left_cancel (hcs63.trans hcs17.symm)) (hae.symm)
        · -- $e \diamond b = c$
          have e1 : e * b = a * b := hcs59.trans hc.symm.symm
          have e2 : e * (a * b) = a * (a * b) := by
            rw [hc.symm]
            exact hv16.trans hd.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs59.trans hv16.symm)) hbc
        · -- $e \diamond b = e$
          have hv75 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs59)).trans hf.symm)).symm.trans (eq677 a b)
          have hv76 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv75.symm)
          rcases hspan (e * e) with hcs77 | hcs77 | hcs77 | hcs77 | hcs77 | hcs77
          · -- $e \diamond e = a$
            have hv78 : f * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                (eq677 a e)).trans hcs77.symm)).trans he.symm.symm)
            have hv79 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs59).trans
                hcs77)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv79.symm.trans hcs77) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs77]; exact hcs59
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs77) (hbe.symm)
          · -- $e \diamond e = c$
            rcases hspan (e * f) with hcs80 | hcs80 | hcs80 | hcs80 | hcs80 | hcs80
            · -- $e \diamond f = a$
              have hv81 : f * e = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs17))).symm.trans
                  (eq677 a e)).trans hcs80.symm)).trans hf.symm.symm)
              exact absurd (mul_left_cancel (hv81.trans hfb.symm)) (hbe.symm)
            · -- $e \diamond f = b$
              have hv82 : b * c = f :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (b * ·)
                  ((congrArg (· * e) hcs59).trans hcs77))).symm.trans
                  (eq677 b e)).trans hcs80.symm)
              have hv83 : c * e = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (e * ·) (congrArg (· * e) hcs77))).symm.trans
                  (eq677 e e)).trans hcs59.symm)).trans hcs80.symm)
              exact absurd (mul_left_cancel (hv83.trans hv76.symm)) (hae.symm)
            · -- $e \diamond f = c$
              exact absurd (mul_left_cancel (hcs80.trans hcs77.symm)) (hef.symm)
            · -- $e \diamond f = d$
              exact absurd (mul_left_cancel (hcs80.trans hv16.symm)) (hcf.symm)
            · -- $e \diamond f = e$
              exact absurd (mul_left_cancel (hcs80.trans hcs59.symm)) (hbf.symm)
            · -- $e \diamond f = f$
              exact absurd (mul_left_cancel (hcs80.trans hcs17.symm)) (haf'.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs77.trans hv16.symm)) (hce.symm)
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs77.trans hcs59.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            exact absurd (mul_left_cancel (hcs77.trans hcs17.symm)) (hae.symm)
        · -- $e \diamond b = f$
          exact absurd (mul_left_cancel (hcs59.trans hcs17.symm)) (hab.symm)
    · -- $f \diamond a = d$
      have hv84 : e * d = d :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
          ((congrArg (· * a) hf.symm).trans hcs1))).symm.trans
          (eq677 e a)).trans he.symm.symm)
      rcases hspan (e * a) with hcs85 | hcs85 | hcs85 | hcs85 | hcs85 | hcs85
      · -- $e \diamond a = a$
        exact absurd hcs85 (hno _)
      · -- $e \diamond a = b$
        have hv86 : d * b = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs85))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs87 | hcs87 | hcs87 | hcs87 | hcs87 | hcs87
        · -- $e \diamond b = a$
          have hv88 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs87)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv88
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          exact absurd (mul_left_cancel (hcs87.trans hcs85.symm)) (hab.symm)
        · -- $e \diamond b = c$
          have e1 : e * a = a * a := hcs85.trans hb.symm.symm
          have e2 : e * (a * a) = a * (a * a) := by
            rw [hb.symm]
            exact hcs87.trans hc.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs87.trans hv84.symm)) hbd
        · -- $e \diamond b = e$
          have hv89 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs87)).trans hf.symm)).symm.trans (eq677 a b)
          have hv90 : e * e = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (b * ·) (congrArg (· * e) hcs87))).symm.trans
              (eq677 b e)).trans hcs85.symm)).trans hv89.symm)
          have hv91 : f * e = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (e * ·) (congrArg (· * e) hv90))).symm.trans
              (eq677 e e)).trans hcs87.symm)).trans hcs85.symm)
          have hv92 : d * f = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
              (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
              (eq677 a f)).trans hv91.symm)).trans he.symm.symm)
          have hv93 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv89.symm)
          have hv94 : d * e = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (d * ·) (congrArg (· * e) hv84))).symm.trans
              (eq677 d e)).trans hv84.symm)).trans hv92.symm)
          have hv95 : d * d = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (f * ·) (congrArg (· * d) hv92))).symm.trans
              (eq677 f d)).trans hv94.symm)).trans hfb.symm)
          have hv96 : b * d = e := by
            have e := eq_cube_of_mul_eq hv84
            rw [hv95] at e
            exact e.symm
          exact absurd (mul_left_cancel (hv96.trans hba.symm)) (had.symm)
        · -- $e \diamond b = f$
          have hv97 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs87)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv97.symm.trans hba) hae
      · -- $e \diamond a = c$
        have hv98 : d * c = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs85))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs99 | hcs99 | hcs99 | hcs99 | hcs99 | hcs99
        · -- $e \diamond b = a$
          have hv100 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs99)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv100
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv101 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs99)).trans hc.symm)).symm.trans (eq677 a b)
          have hv102 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv101.symm)
          have hv103 : c * d = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (c * ·) (congrArg (· * d) hv98))).symm.trans
              (eq677 c d)).trans hv98.symm)).trans hv102.symm)
          have hv104 : c * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hv102))).symm.trans
              (eq677 a c)).trans hv103.symm)).trans hd.symm.symm)
          exact absurd (mul_left_cancel (hv104.trans hv102.symm)) (hac.symm)
        · -- $e \diamond b = c$
          exact absurd (mul_left_cancel (hcs99.trans hcs85.symm)) (hab.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs99.trans hv84.symm)) hbd
        · -- $e \diamond b = e$
          have hv105 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs99)).trans hf.symm)).symm.trans (eq677 a b)
          have hv106 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv105.symm)
          rcases hspan (e * e) with hcs107 | hcs107 | hcs107 | hcs107 | hcs107 | hcs107
          · -- $e \diamond e = a$
            have hv108 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs85))).symm.trans
                (eq677 a e)).trans hcs107.symm)).trans he.symm.symm)
            have hv109 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs99).trans
                hcs107)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv109.symm.trans hcs107) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs107]; exact hcs99
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs107) (hbe.symm)
          · -- $e \diamond e = c$
            exact absurd (mul_left_cancel (hcs107.trans hcs85.symm)) (hae.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs107.trans hv84.symm)) (hde.symm)
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs107.trans hcs99.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            have hv110 : e * a = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs99).trans
                hcs107)).trans hv105)).symm.trans (eq677 b e)
            exact absurd (hv110.symm.trans hcs85) hbc
        · -- $e \diamond b = f$
          have hv111 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs99)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv111.symm.trans hba) hae
      · -- $e \diamond a = d$
        exact absurd (mul_left_cancel (hcs85.trans hv84.symm)) had
      · -- $e \diamond a = e$
        have hv112 : d * e = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs85))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv113 : d * c = d := by
          have e := mul_mul_eq_self_of_mul_eq hv84
          rw [hv112] at e
          exact e
        rcases hspan (d * a) with hcs114 | hcs114 | hcs114 | hcs114 | hcs114 | hcs114
        · -- $d \diamond a = a$
          exact absurd hcs114 (hno _)
        · -- $d \diamond a = b$
          have hv115 : c * b = b :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
              ((congrArg (· * a) hd.symm).trans hcs114))).symm.trans
              (eq677 c a)).trans hc.symm.symm)
          rcases hspan (d * b) with hcs116 | hcs116 | hcs116 | hcs116 | hcs116 | hcs116
          · -- $d \diamond b = a$
            have hv117 : b * d = a :=
              mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                (congrArg (a * ·) (congrArg (· * d) hcs114))).symm.trans
                (eq677 a d)).trans hcs116.symm)).trans hb.symm.symm)
            have hv118 : b * e = a :=
              mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                ((congrArg (· * d) hcs116).trans he.symm))).symm.trans
                (eq677 b d)).trans hcs114.symm)
            exact absurd (mul_left_cancel (hv118.trans hv117.symm)) (hde.symm)
          · -- $d \diamond b = b$
            exact absurd (mul_left_cancel (hcs116.trans hcs114.symm)) (hab.symm)
          · -- $d \diamond b = c$
            exact absurd (mul_left_cancel (hcs116.trans hv112.symm)) hbe
          · -- $d \diamond b = d$
            exact absurd (mul_left_cancel (hcs116.trans hv113.symm)) hbc
          · -- $d \diamond b = e$
            have hv119 : b * d = a :=
              mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                ((congrArg (· * d) hcs116).trans hv84))).symm.trans
                (eq677 b d)).trans hcs114.symm)
            have hv120 : c * a = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
                (eq677 b a)).trans hb.symm.symm)).trans hv119.symm)
            have hv121 : e * b = c :=
              mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
                (eq677 a b)).trans hv119.symm)).trans hd.symm.symm)
            have hv122 : b * d = d :=
              (congrArg (b * ·) ((congrArg (d * ·) ((congrArg (· * b) hv119).trans
                hc.symm)).trans hv113)).symm.trans (eq677 d b)
            exact absurd (hv122.symm.trans hv119) (had.symm)
          · -- $d \diamond b = f$
            rcases hspan (d * f) with hcs123 | hcs123 | hcs123 | hcs123 | hcs123 | hcs123
            · -- $d \diamond f = a$
              have e1 : d * f = a * f := hcs123.trans haf.symm
              have e2 : d * (a * f) = a * (a * f) := by
                rw [haf]
                exact hcs114.trans hb.symm.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (had.symm)
            · -- $d \diamond f = b$
              exact absurd (mul_left_cancel (hcs123.trans hcs114.symm)) (haf'.symm)
            · -- $d \diamond f = c$
              exact absurd (mul_left_cancel (hcs123.trans hv112.symm)) (hef.symm)
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs123.trans hv113.symm)) (hcf.symm)
            · -- $d \diamond f = e$
              have hv124 : f * f = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs123)).trans hf.symm)).symm.trans (eq677 a f)
              have hv125 : f * d = f :=
                (congrArg (f * ·) ((congrArg (f * ·) ((congrArg (· * f) hv124).trans
                  haf)).trans hcs1)).symm.trans (eq677 f f)
              have e : f * (f * (f * f)) = f := by rw [hv124, hcs1]; exact hv125
              exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hv124) (haf'.symm)
            · -- $d \diamond f = f$
              exact absurd (mul_left_cancel (hcs123.trans hcs116.symm)) (hbf.symm)
        · -- $d \diamond a = c$
          exact absurd (mul_left_cancel (hcs114.trans hv112.symm)) hae
        · -- $d \diamond a = d$
          exact absurd (mul_left_cancel (hcs114.trans hv113.symm)) hac
        · -- $d \diamond a = e$
          have hv126 : c * e = b :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
              ((congrArg (· * a) hd.symm).trans hcs114))).symm.trans
              (eq677 c a)).trans hc.symm.symm)
          have hv127 : d * e = a :=
            (congrArg (d * ·) ((congrArg (a * ·) ((congrArg (· * d) hcs114).trans
              hv84)).trans he.symm)).symm.trans (eq677 a d)
          exact absurd (hv127.symm.trans hv112) hac
        · -- $d \diamond a = f$
          have hv128 : c * f = b :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
              ((congrArg (· * a) hd.symm).trans hcs114))).symm.trans
              (eq677 c a)).trans hc.symm.symm)
          rcases hspan (d * b) with hcs129 | hcs129 | hcs129 | hcs129 | hcs129 | hcs129
          · -- $d \diamond b = a$
            have hv130 : f * d = a :=
              mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                (congrArg (a * ·) (congrArg (· * d) hcs114))).symm.trans
                (eq677 a d)).trans hcs129.symm)).trans hb.symm.symm)
            have hv131 : d * f = c :=
              mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
                (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
                (eq677 a f)).trans hv130.symm)).trans hd.symm.symm)
            exact absurd (mul_left_cancel (hv131.trans hv112.symm)) (hef.symm)
          · -- $d \diamond b = b$
            rcases hspan (d * f) with hcs132 | hcs132 | hcs132 | hcs132 | hcs132 | hcs132
            · -- $d \diamond f = a$
              have hv133 : f * b = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs132)).trans hb.symm)).symm.trans (eq677 a f)
              exact absurd (hv133.symm.trans hfb) hae
            · -- $d \diamond f = b$
              exact absurd (mul_left_cancel (hcs132.trans hcs129.symm)) (hbf.symm)
            · -- $d \diamond f = c$
              exact absurd (mul_left_cancel (hcs132.trans hv112.symm)) (hef.symm)
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs132.trans hv113.symm)) (hcf.symm)
            · -- $d \diamond f = e$
              have hv134 : f * f = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs132)).trans hf.symm)).symm.trans (eq677 a f)
              have hv135 : f * d = f :=
                (congrArg (f * ·) ((congrArg (f * ·) ((congrArg (· * f) hv134).trans
                  haf)).trans hcs1)).symm.trans (eq677 f f)
              have e : f * (f * (f * f)) = f := by rw [hv134, hcs1]; exact hv135
              exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hv134) (haf'.symm)
            · -- $d \diamond f = f$
              exact absurd (mul_left_cancel (hcs132.trans hcs114.symm)) (haf'.symm)
          · -- $d \diamond b = c$
            exact absurd (mul_left_cancel (hcs129.trans hv112.symm)) hbe
          · -- $d \diamond b = d$
            exact absurd (mul_left_cancel (hcs129.trans hv113.symm)) hbc
          · -- $d \diamond b = e$
            rcases hspan (d * f) with hcs136 | hcs136 | hcs136 | hcs136 | hcs136 | hcs136
            · -- $d \diamond f = a$
              have hv137 : f * b = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs136)).trans hb.symm)).symm.trans (eq677 a f)
              exact absurd (hv137.symm.trans hfb) hae
            · -- $d \diamond f = b$
              have hv138 : f * c = a :=
                (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
                  hcs136)).trans hc.symm)).symm.trans (eq677 a f)
              have hv139 : b * d = f :=
                mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                  ((congrArg (· * d) hcs129).trans hv84))).symm.trans
                  (eq677 b d)).trans hcs136.symm)
              have hv140 : f * f = a :=
                mul_left_cancel (((congrArg (d * ·) (congrArg (f * ·)
                  ((congrArg (· * d) hcs136).trans hv139))).symm.trans
                  (eq677 f d)).trans hcs114.symm)
              exact absurd (mul_left_cancel (hv140.trans hv138.symm)) (hcf.symm)
            · -- $d \diamond f = c$
              exact absurd (mul_left_cancel (hcs136.trans hv112.symm)) (hef.symm)
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs136.trans hv113.symm)) (hcf.symm)
            · -- $d \diamond f = e$
              exact absurd (mul_left_cancel (hcs136.trans hcs129.symm)) (hbf.symm)
            · -- $d \diamond f = f$
              exact absurd (mul_left_cancel (hcs136.trans hcs114.symm)) (haf'.symm)
          · -- $d \diamond b = f$
            exact absurd (mul_left_cancel (hcs129.trans hcs114.symm)) (hab.symm)
      · -- $e \diamond a = f$
        have hv141 : d * f = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs85))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        have hv142 : f * d = a :=
          (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hcs1).trans
            hv141)).trans hd.symm)).symm.trans (eq677 a f)
        have hv143 : d * a = a :=
          mul_left_cancel (((congrArg (f * ·) (congrArg (d * ·)
            ((congrArg (· * f) hv142).trans haf))).symm.trans
            (eq677 d f)).trans hcs1.symm)
        exact absurd hv143 (hno _)
    · -- $f \diamond a = e$
      exact absurd (mul_left_cancel (hcs1.trans hfb.symm)) hab
    · -- $f \diamond a = f$
      have hv144 : e * f = d :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
          ((congrArg (· * a) hf.symm).trans hcs1))).symm.trans
          (eq677 e a)).trans he.symm.symm)
      rcases hspan (e * a) with hcs145 | hcs145 | hcs145 | hcs145 | hcs145 | hcs145
      · -- $e \diamond a = a$
        exact absurd hcs145 (hno _)
      · -- $e \diamond a = b$
        have hv146 : d * b = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs145))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs147 | hcs147 | hcs147 | hcs147 | hcs147 | hcs147
        · -- $e \diamond b = a$
          have hv148 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs147)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv148
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          exact absurd (mul_left_cancel (hcs147.trans hcs145.symm)) (hab.symm)
        · -- $e \diamond b = c$
          have e1 : e * a = a * a := hcs145.trans hb.symm.symm
          have e2 : e * (a * a) = a * (a * a) := by
            rw [hb.symm]
            exact hcs147.trans hc.symm.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hae.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs147.trans hv144.symm)) hbf
        · -- $e \diamond b = e$
          have hv149 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs147)).trans hf.symm)).symm.trans (eq677 a b)
          have hv150 : e * e = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (b * ·) (congrArg (· * e) hcs147))).symm.trans
              (eq677 b e)).trans hcs145.symm)).trans hv149.symm)
          have hv151 : f * e = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (e * ·) (congrArg (· * e) hv150))).symm.trans
              (eq677 e e)).trans hcs147.symm)).trans hcs145.symm)
          have hv152 : d * e = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
              (congrArg (f * ·) (congrArg (· * e) hv144))).symm.trans
              (eq677 f e)).trans hv150.symm)).trans hfb.symm)
          have hv153 : f * f = d :=
            mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
              (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
              (eq677 a f)).trans hv151.symm)).trans he.symm.symm)
          have hv154 : d * f = e :=
            mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
              (congrArg (f * ·) (congrArg (· * f) hv153))).symm.trans
              (eq677 f f)).trans hcs1.symm)).trans hv151.symm)
          have hv155 : c * d = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (b * ·) (congrArg (· * d) hv146))).symm.trans
              (eq677 b d)).trans hv152.symm)).trans hba.symm)
          have hv156 : b * d = e :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (e * ·) (congrArg (· * d) hv152))).symm.trans
              (eq677 e d)).trans hv154.symm)).trans hv150.symm)
          exact absurd (mul_left_cancel (hv156.trans hba.symm)) (had.symm)
        · -- $e \diamond b = f$
          have hv157 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs147)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv157.symm.trans hba) hae
      · -- $e \diamond a = c$
        have hv158 : d * c = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs145))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs159 | hcs159 | hcs159 | hcs159 | hcs159 | hcs159
        · -- $e \diamond b = a$
          have hv160 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs159)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv160
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv161 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs159)).trans hc.symm)).symm.trans (eq677 a b)
          have hv162 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv161.symm)
          have hv163 : c * d = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (c * ·) (congrArg (· * d) hv158))).symm.trans
              (eq677 c d)).trans hv158.symm)).trans hv162.symm)
          have hv164 : c * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hv162))).symm.trans
              (eq677 a c)).trans hv163.symm)).trans hd.symm.symm)
          exact absurd (mul_left_cancel (hv164.trans hv162.symm)) (hac.symm)
        · -- $e \diamond b = c$
          exact absurd (mul_left_cancel (hcs159.trans hcs145.symm)) (hab.symm)
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs159.trans hv144.symm)) hbf
        · -- $e \diamond b = e$
          have hv165 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs159)).trans hf.symm)).symm.trans (eq677 a b)
          have hv166 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv165.symm)
          rcases hspan (e * e) with hcs167 | hcs167 | hcs167 | hcs167 | hcs167 | hcs167
          · -- $e \diamond e = a$
            have hv168 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                (eq677 a e)).trans hcs167.symm)).trans he.symm.symm)
            have hv169 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs159).trans
                hcs167)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv169.symm.trans hcs167) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs167]; exact hcs159
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs167) (hbe.symm)
          · -- $e \diamond e = c$
            exact absurd (mul_left_cancel (hcs167.trans hcs145.symm)) (hae.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs167.trans hv144.symm)) hef
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs167.trans hcs159.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            have hv170 : e * a = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs159).trans
                hcs167)).trans hv165)).symm.trans (eq677 b e)
            exact absurd (hv170.symm.trans hcs145) hbc
        · -- $e \diamond b = f$
          have hv171 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs159)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv171.symm.trans hba) hae
      · -- $e \diamond a = d$
        exact absurd (mul_left_cancel (hcs145.trans hv144.symm)) haf'
      · -- $e \diamond a = e$
        have hv172 : d * e = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs145))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs173 | hcs173 | hcs173 | hcs173 | hcs173 | hcs173
        · -- $e \diamond b = a$
          have hv174 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs173)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv174
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv175 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs173)).trans hc.symm)).symm.trans (eq677 a b)
          have hv176 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv175.symm)
          rcases hspan (e * e) with hcs177 | hcs177 | hcs177 | hcs177 | hcs177 | hcs177
          · -- $e \diamond e = a$
            have e : e * (e * e) = e := by rw [hcs177]; exact hcs145
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs177) (hae.symm)
          · -- $e \diamond e = b$
            exact absurd (mul_left_cancel (hcs177.trans hcs173.symm)) (hbe.symm)
          · -- $e \diamond e = c$
            have hv178 : e * d = a :=
              (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs145).trans
                hcs177)).trans hd.symm)).symm.trans (eq677 a e)
            have hv179 : c * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (e * ·) (congrArg (· * e) hcs177))).symm.trans
                (eq677 e e)).trans hcs145.symm)).trans hv178.symm)
            have hv180 : d * f = f :=
              mul_left_cancel (((congrArg (e * ·) (congrArg (d * ·)
                ((congrArg (· * e) hv178).trans hf.symm))).symm.trans
                (eq677 d e)).trans hv144.symm)
            have hv181 : f * d = a :=
              mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                (congrArg (f * ·) (congrArg (· * d) hv180))).symm.trans
                (eq677 f d)).trans hv180.symm)).trans hcs1.symm)
            have hv182 : e * c = f := by
              rcases hspan (e * c) with hz | hz | hz | hz | hz | hz
              · exact absurd (mul_left_cancel (hz.trans hv178.symm)) hcd
              · exact absurd (mul_left_cancel (hz.trans hcs173.symm)) (hbc.symm)
              · exact absurd (mul_left_cancel (hz.trans hcs177.symm)) hce
              · exact absurd (mul_left_cancel (hz.trans hv144.symm)) hcf
              · exact absurd (mul_left_cancel (hz.trans hcs145.symm)) (hac.symm)
              · exact hz
            have hv183 : f * c = c :=
              mul_left_cancel (((congrArg (e * ·) (congrArg (f * ·)
                ((congrArg (· * e) hv144).trans hv172))).symm.trans
                (eq677 f e)).trans hv182.symm)
            have hv184 : f * f = c :=
              mul_left_cancel ((mul_left_cancel (((congrArg (f * ·)
                (congrArg (a * ·) (congrArg (· * f) hcs1))).symm.trans
                (eq677 a f)).trans hv181.symm)).trans hd.symm.symm)
            exact absurd (mul_left_cancel (hv184.trans hv183.symm)) (hcf.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs177.trans hv144.symm)) hef
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs177.trans hcs145.symm)) (hae.symm)
          · -- $e \diamond e = f$
            have hv185 : e * a = a :=
              (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hcs145).trans
                hcs177)).trans haf)).symm.trans (eq677 a e)
            exact absurd (hv185.symm.trans hcs145) hae
        · -- $e \diamond b = c$
          have hv186 : b * d = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs173)).trans hd.symm)).symm.trans (eq677 a b)
          have hv187 : f * a = b :=
            (congrArg (f * ·) ((congrArg (b * ·) ((congrArg (· * f) hfb).trans
              hv144)).trans hv186)).symm.trans (eq677 b f)
          exact absurd (hv187.symm.trans hcs1) hbf
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs173.trans hv144.symm)) hbf
        · -- $e \diamond b = e$
          exact absurd (mul_left_cancel (hcs173.trans hcs145.symm)) (hab.symm)
        · -- $e \diamond b = f$
          have hv188 : b * a = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs173)).trans haf)).symm.trans (eq677 a b)
          exact absurd (hv188.symm.trans hba) hae
      · -- $e \diamond a = f$
        have hv189 : d * f = c :=
          mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
            ((congrArg (· * a) he.symm).trans hcs145))).symm.trans
            (eq677 d a)).trans hd.symm.symm)
        rcases hspan (e * b) with hcs190 | hcs190 | hcs190 | hcs190 | hcs190 | hcs190
        · -- $e \diamond b = a$
          have hv191 : b * b = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs190)).trans hb.symm)).symm.trans (eq677 a b)
          have e : a * a * (a * a) = a := by rw [hb.symm]; exact hv191
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hb.symm) hab
        · -- $e \diamond b = b$
          have hv192 : b * c = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs190)).trans hc.symm)).symm.trans (eq677 a b)
          have hv193 : c * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv192.symm)
          rcases hspan (e * e) with hcs194 | hcs194 | hcs194 | hcs194 | hcs194 | hcs194
          · -- $e \diamond e = a$
            have hv195 : f * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                (eq677 a e)).trans hcs194.symm)).trans he.symm.symm)
            have hv196 : e * d = e :=
              (congrArg (e * ·) ((congrArg (e * ·) ((congrArg (· * e) hcs194).trans
                hf.symm)).trans hv144)).symm.trans (eq677 e e)
            have hv197 : d * a = f :=
              mul_left_cancel (((congrArg (e * ·) (congrArg (d * ·)
                ((congrArg (· * e) hv196).trans hcs194))).symm.trans
                (eq677 d e)).trans hv144.symm)
            have hv198 : e * c = b :=
              mul_left_cancel (((congrArg (f * ·) (congrArg (e * ·)
                ((congrArg (· * f) hv195).trans hv189))).symm.trans
                (eq677 e f)).trans hfb.symm)
            exact absurd (mul_left_cancel (hv198.trans hcs190.symm)) (hbc.symm)
          · -- $e \diamond e = b$
            exact absurd (mul_left_cancel (hcs194.trans hcs190.symm)) (hbe.symm)
          · -- $e \diamond e = c$
            rcases hspan (e * c) with hcs199 | hcs199 | hcs199 | hcs199 | hcs199 | hcs199
            · -- $e \diamond c = a$
              have hv200 : f * e = b :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                  (eq677 a e)).trans hcs199.symm)).trans hc.symm.symm)
              have hv201 : c * f = e :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                  ((congrArg (· * e) hcs199).trans hf.symm))).symm.trans
                  (eq677 c e)).trans hcs194.symm)
              have hv202 : b * d = e :=
                mul_left_cancel (((congrArg (f * ·) (congrArg (b * ·)
                  ((congrArg (· * f) hfb).trans hv144))).symm.trans
                  (eq677 b f)).trans hv200.symm)
              exact absurd (mul_left_cancel (hv202.trans hba.symm)) (had.symm)
            · -- $e \diamond c = b$
              exact absurd (mul_left_cancel (hcs199.trans hcs190.symm)) (hbc.symm)
            · -- $e \diamond c = c$
              exact absurd (mul_left_cancel (hcs199.trans hcs194.symm)) hce
            · -- $e \diamond c = d$
              exact absurd (mul_left_cancel (hcs199.trans hv144.symm)) hcf
            · -- $e \diamond c = e$
              have e : e * (e * e) = e := by rw [hcs194]; exact hcs199
              exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs194) (hce.symm)
            · -- $e \diamond c = f$
              exact absurd (mul_left_cancel (hcs199.trans hcs145.symm)) (hac.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs194.trans hv144.symm)) hef
          · -- $e \diamond e = e$
            rcases hspan (e * c) with hcs203 | hcs203 | hcs203 | hcs203 | hcs203 | hcs203
            · -- $e \diamond c = a$
              have hv204 : f * e = b :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                  (eq677 a e)).trans hcs203.symm)).trans hc.symm.symm)
              have hv205 : b * d = e :=
                mul_left_cancel (((congrArg (f * ·) (congrArg (b * ·)
                  ((congrArg (· * f) hfb).trans hv144))).symm.trans
                  (eq677 b f)).trans hv204.symm)
              exact absurd (mul_left_cancel (hv205.trans hba.symm)) (had.symm)
            · -- $e \diamond c = b$
              exact absurd (mul_left_cancel (hcs203.trans hcs190.symm)) (hbc.symm)
            · -- $e \diamond c = c$
              have hv206 : c * e = a :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (c * ·) (congrArg (· * e) hcs203))).symm.trans
                  (eq677 c e)).trans hcs203.symm)).trans hv193.symm)
              have hv207 : c * c = d :=
                mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
                  (congrArg (a * ·) (congrArg (· * c) hv193))).symm.trans
                  (eq677 a c)).trans hv206.symm)).trans he.symm.symm)
              have hv208 : d * c = e := by
                have e := eq_cube_of_mul_eq hcs203
                rw [hv207] at e
                exact e.symm
              have hv209 : e * d = a := by
                rcases hspan (e * d) with hz | hz | hz | hz | hz | hz
                · exact hz
                · exact absurd (mul_left_cancel (hz.trans hcs190.symm)) (hbd.symm)
                · exact absurd (mul_left_cancel (hz.trans hcs203.symm)) (hcd.symm)
                · exact absurd (mul_left_cancel (hz.trans hv144.symm)) hdf
                · exact absurd (mul_left_cancel (hz.trans hcs194.symm)) hde
                · exact absurd (mul_left_cancel (hz.trans hcs145.symm)) (had.symm)
              have hv210 : b * d = c :=
                (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hv192).trans
                  hc.symm)).trans hv207)).symm.trans (eq677 c b)
              have hv211 : f * e = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                  (eq677 a e)).trans hv209.symm)).trans hd.symm.symm)
              have hv212 : e * c = d :=
                (congrArg (e * ·) ((congrArg (d * ·) ((congrArg (· * e) hv209).trans
                  hf.symm)).trans hv189)).symm.trans (eq677 d e)
              exact absurd (hv212.symm.trans hcs203) (hcd.symm)
            · -- $e \diamond c = d$
              exact absurd (mul_left_cancel (hcs203.trans hv144.symm)) hcf
            · -- $e \diamond c = e$
              exact absurd (mul_left_cancel (hcs203.trans hcs194.symm)) hce
            · -- $e \diamond c = f$
              exact absurd (mul_left_cancel (hcs203.trans hcs145.symm)) (hac.symm)
          · -- $e \diamond e = f$
            exact absurd (mul_left_cancel (hcs194.trans hcs145.symm)) (hae.symm)
        · -- $e \diamond b = c$
          have hv213 : b * d = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs190)).trans hd.symm)).symm.trans (eq677 a b)
          have hv214 : f * a = b :=
            (congrArg (f * ·) ((congrArg (b * ·) ((congrArg (· * f) hfb).trans
              hv144)).trans hv213)).symm.trans (eq677 b f)
          exact absurd (hv214.symm.trans hcs1) hbf
        · -- $e \diamond b = d$
          exact absurd (mul_left_cancel (hcs190.trans hv144.symm)) hbf
        · -- $e \diamond b = e$
          have hv215 : b * f = a :=
            (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hba).trans
              hcs190)).trans hf.symm)).symm.trans (eq677 a b)
          have hv216 : c * a = f :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
              (eq677 b a)).trans hb.symm.symm)).trans hv215.symm)
          rcases hspan (e * e) with hcs217 | hcs217 | hcs217 | hcs217 | hcs217 | hcs217
          · -- $e \diamond e = a$
            have hv218 : f * e = d :=
              mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                (eq677 a e)).trans hcs217.symm)).trans he.symm.symm)
            have hv219 : e * e = b :=
              (congrArg (e * ·) ((congrArg (b * ·) ((congrArg (· * e) hcs190).trans
                hcs217)).trans hba)).symm.trans (eq677 b e)
            exact absurd (hv219.symm.trans hcs217) (hab.symm)
          · -- $e \diamond e = b$
            have e : e * (e * e) = e := by rw [hcs217]; exact hcs190
            exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs217) (hbe.symm)
          · -- $e \diamond e = c$
            rcases hspan (e * c) with hcs220 | hcs220 | hcs220 | hcs220 | hcs220 | hcs220
            · -- $e \diamond c = a$
              have hv221 : f * e = b :=
                mul_left_cancel ((mul_left_cancel (((congrArg (e * ·)
                  (congrArg (a * ·) (congrArg (· * e) hcs145))).symm.trans
                  (eq677 a e)).trans hcs220.symm)).trans hc.symm.symm)
              have hv222 : c * f = e :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                  ((congrArg (· * e) hcs220).trans hf.symm))).symm.trans
                  (eq677 c e)).trans hcs217.symm)
              have hv223 : b * d = e :=
                mul_left_cancel (((congrArg (f * ·) (congrArg (b * ·)
                  ((congrArg (· * f) hfb).trans hv144))).symm.trans
                  (eq677 b f)).trans hv221.symm)
              exact absurd (mul_left_cancel (hv223.trans hba.symm)) (had.symm)
            · -- $e \diamond c = b$
              have e : e * (e * (e * e)) = e := by rw [hcs217, hcs220]; exact hcs190
              exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hcs217) (hce.symm)
            · -- $e \diamond c = c$
              exact absurd (mul_left_cancel (hcs220.trans hcs217.symm)) hce
            · -- $e \diamond c = d$
              exact absurd (mul_left_cancel (hcs220.trans hv144.symm)) hcf
            · -- $e \diamond c = e$
              exact absurd (mul_left_cancel (hcs220.trans hcs190.symm)) (hbc.symm)
            · -- $e \diamond c = f$
              exact absurd (mul_left_cancel (hcs220.trans hcs145.symm)) (hac.symm)
          · -- $e \diamond e = d$
            exact absurd (mul_left_cancel (hcs217.trans hv144.symm)) hef
          · -- $e \diamond e = e$
            exact absurd (mul_left_cancel (hcs217.trans hcs190.symm)) (hbe.symm)
          · -- $e \diamond e = f$
            exact absurd (mul_left_cancel (hcs217.trans hcs145.symm)) (hae.symm)
        · -- $e \diamond b = f$
          exact absurd (mul_left_cancel (hcs190.trans hcs145.symm)) (hab.symm)

/-- **At order six, $L_a$ fixes no point but $a$.**

If $a \diamond m = m$ then $a$ is a left unit of $m$, hence its cube $a = (m \diamond m) \diamond m$
(`eq_cube_of_mul_eq`), and $m$ satisfies Equation 255. An idempotent $m$ is its own cube, so then
$a = m$. Otherwise the degree of $m$ is at most $6$; it is not $1$, $2$ or $3$, it is not $4$ or
$5$ because $m$ satisfies Equation 255, and it is not $6$ by
`not_hasDeg_six_of_card_eq_six`. -/
theorem eq_of_mul_eq_self_of_card_eq_six (hM : Finite.card M = 6) {a m : M} (h : a * m = m) :
    a = m := by
  have hcube : a = m * m * m := eq_cube_of_mul_eq h
  have h255 : Eq255At m := eq255At_of_exists_mul_eq ⟨a, h⟩
  by_cases hid : IsIdempotentElem m
  · rw [hcube, hid.eq, hid.eq]
  · obtain ⟨n, hn, hdeg⟩ := exists_hasDeg m
    rw [hM] at hn
    have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
      have := hdeg.1
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hid hdeg.2.1).elim
    · exact absurd hdeg (not_hasDeg_two m)
    · exact absurd hdeg (not_hasDeg_three m)
    · exact absurd hdeg (not_hasDeg_four_of_eq255At h255)
    · exact absurd hdeg (not_hasDeg_five_of_eq255At h255)
    · exact absurd hdeg (not_hasDeg_six_of_card_eq_six hM m)

/-- **A six-element magma has no element of degree $5$.**

The orbit $a, b, c, d, e$ of $a$ under $L_a$ misses exactly one point $m$. Since $L_a$ is a
bijection mapping the orbit onto itself, it maps $m$ to $m$; and
`eq_of_mul_eq_self_of_card_eq_six` forbids a fixed point $m \neq a$. -/
theorem not_hasDeg_five_of_card_eq_six (hM : Finite.card M = 6) (a : M) : ¬ HasDeg a 5 := by
  intro hdeg
  -- one turn of the orbit, named
  obtain ⟨b, hb⟩ : ∃ b, b = a * a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = a * c := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = a * d := ⟨_, rfl⟩
  -- the turn closes up: $L_a(e) = a$
  have hae0 : a * e = a := by
    rw [he, hd, hc, hb]
    exact hdeg.2.1
  -- distinctness of one turn
  have hNE : ∀ m n : Nat, m < 5 → n < 5 → m ≠ n →
      leftApplyMul a a m ≠ leftApplyMul a a n := fun _ _ hm hn hmn => hdeg.ne hm hn hmn
  have hab : a ≠ b := by rw [hb]; exact hNE 0 1 (by omega) (by omega) (by omega)
  have hac : a ≠ c := by rw [hc, hb]; exact hNE 0 2 (by omega) (by omega) (by omega)
  have had : a ≠ d := by rw [hd, hc, hb]; exact hNE 0 3 (by omega) (by omega) (by omega)
  have hae : a ≠ e := by rw [he, hd, hc, hb]; exact hNE 0 4 (by omega) (by omega) (by omega)
  have hbc : b ≠ c := by rw [hc, hb]; exact hNE 1 2 (by omega) (by omega) (by omega)
  have hbd : b ≠ d := by rw [hd, hc, hb]; exact hNE 1 3 (by omega) (by omega) (by omega)
  have hbe : b ≠ e := by rw [he, hd, hc, hb]; exact hNE 1 4 (by omega) (by omega) (by omega)
  have hcd : c ≠ d := by rw [hd, hc, hb]; exact hNE 2 3 (by omega) (by omega) (by omega)
  have hce : c ≠ e := by rw [he, hd, hc, hb]; exact hNE 2 4 (by omega) (by omega) (by omega)
  have hde : d ≠ e := by rw [he, hd, hc, hb]; exact hNE 3 4 (by omega) (by omega) (by omega)
  -- the one point the orbit misses
  obtain ⟨m, hm⟩ := Finite.exists_notMem (l := [a, b, c, d, e])
    (by simp [hM])
  have ham : a ≠ m := fun h => hm (by rw [h]; simp)
  have hbm : b ≠ m := fun h => hm (by rw [h]; simp)
  have hcm : c ≠ m := fun h => hm (by rw [h]; simp)
  have hdm : d ≠ m := fun h => hm (by rw [h]; simp)
  have hem : e ≠ m := fun h => hm (by rw [h]; simp)
  have hspan : ∀ z : M, z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = m :=
    Finite.span_six hM hab hac had hae ham hbc hbd hbe hbm hcd hce hcm hde hdm hem
  -- $L_a$ maps the orbit onto itself, so it fixes $m$
  rcases hspan (a * m) with h | h | h | h | h | h
  · -- $a \diamond m = a = a \diamond e$
    exact hem (mul_left_cancel (hae0.trans h.symm))
  · -- $a \diamond m = b = a \diamond a$
    exact ham (mul_left_cancel (h.trans hb)).symm
  · -- $a \diamond m = c = a \diamond b$
    exact hbm (mul_left_cancel (h.trans hc)).symm
  · -- $a \diamond m = d = a \diamond c$
    exact hcm (mul_left_cancel (h.trans hd)).symm
  · -- $a \diamond m = e = a \diamond d$
    exact hdm (mul_left_cancel (h.trans he)).symm
  · -- $a \diamond m = m$
    exact ham (eq_of_mul_eq_self_of_card_eq_six hM h)

/-- **A six-element magma has no element of degree $4$.**

The orbit $a, b, c, d$ of $a$ under $L_a$ misses two points $u, v$, which $L_a$ permutes. A fixed
one is forbidden by `eq_of_mul_eq_self_of_card_eq_six`, so $L_a$ swaps them. In that
configuration Equation 255 fails at $a$ — it would make $a$ idempotent through
`isIdempotentElem_of_mul_sq_eq_sq_mul`, as $L_a^4(a) = a$ — so no element is a left unit for $a$,
and a case analysis over the cell $d \diamond a$ and the row of $c$ refutes the table. -/
theorem not_hasDeg_four_of_card_eq_six (hM : Finite.card M = 6) (a : M) : ¬ HasDeg a 4 := by
  intro hdeg
  have hnid : ¬ IsIdempotentElem a := fun h => hdeg.2.2 1 (by decide) (by decide) h
  -- one turn of the orbit, named
  obtain ⟨b, hb⟩ : ∃ b, b = a * a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = a * c := ⟨_, rfl⟩
  -- the turn closes up: $L_a(d) = a$
  have had0 : a * d = a := by
    rw [hd, hc, hb]
    exact hdeg.2.1
  -- the two backward names: $d = a / a$ and $c = (a \diamond a) \diamond a$
  have hDdiv : d = a / a := (div_eq_iff_mul_eq.mpr had0).symm
  have hCcube : c = a * a * a :=
    (div_eq_iff_mul_eq.mpr (hd.symm.trans hDdiv)).symm.trans div_div_eq_mul_mul
  -- the two seeded cells: the cube is $b \diamond a$, and `div_self_mul_sq`
  have hba : b * a = c := by rw [hCcube, hb]
  have hdb : d * b = c := by rw [hDdiv, hb, hCcube]; exact div_self_mul_sq a
  -- distinctness of one turn
  have hNE : ∀ m n : Nat, m < 4 → n < 4 → m ≠ n →
      leftApplyMul a a m ≠ leftApplyMul a a n := fun _ _ hm hn hmn => hdeg.ne hm hn hmn
  have hab : a ≠ b := by rw [hb]; exact hNE 0 1 (by omega) (by omega) (by omega)
  have hac : a ≠ c := by rw [hc, hb]; exact hNE 0 2 (by omega) (by omega) (by omega)
  have had : a ≠ d := by rw [hd, hc, hb]; exact hNE 0 3 (by omega) (by omega) (by omega)
  have hbc : b ≠ c := by rw [hc, hb]; exact hNE 1 2 (by omega) (by omega) (by omega)
  have hbd : b ≠ d := by rw [hd, hc, hb]; exact hNE 1 3 (by omega) (by omega) (by omega)
  have hcd : c ≠ d := by rw [hd, hc, hb]; exact hNE 2 3 (by omega) (by omega) (by omega)
  -- the two points the orbit misses
  obtain ⟨u, hu⟩ := Finite.exists_notMem (l := [a, b, c, d])
    (by simp [hM])
  obtain ⟨v, hv⟩ := Finite.exists_notMem (l := [u, a, b, c, d])
    (by simp [hM])
  have hau : a ≠ u := fun h => hu (by rw [h]; simp)
  have hbu : b ≠ u := fun h => hu (by rw [h]; simp)
  have hcu : c ≠ u := fun h => hu (by rw [h]; simp)
  have hdu : d ≠ u := fun h => hu (by rw [h]; simp)
  have huv : u ≠ v := fun h => hv (by rw [h]; simp)
  have hav : a ≠ v := fun h => hv (by rw [h]; simp)
  have hbv : b ≠ v := fun h => hv (by rw [h]; simp)
  have hcv : c ≠ v := fun h => hv (by rw [h]; simp)
  have hdv : d ≠ v := fun h => hv (by rw [h]; simp)
  -- the six elements exhaust the carrier
  have hspan : ∀ z : M, z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = u ∨ z = v :=
    Finite.span_six hM hab hac had hau hav hbc hbd hbu hbv hcd hcu hcv hdu hdv huv
  -- $L_a$ maps the orbit onto itself, so it permutes $\{u, v\}$, and it fixes neither
  have hauv : a * u = v := by
    rcases hspan (a * u) with h | h | h | h | h | h
    · exact absurd (mul_left_cancel (had0.trans h.symm)) hdu
    · exact absurd (mul_left_cancel (h.trans hb)).symm hau
    · exact absurd (mul_left_cancel (h.trans hc)).symm hbu
    · exact absurd (mul_left_cancel (h.trans hd)).symm hcu
    · exact absurd (eq_of_mul_eq_self_of_card_eq_six hM h) hau
    · exact h
  have havu : a * v = u := by
    rcases hspan (a * v) with h | h | h | h | h | h
    · exact absurd (mul_left_cancel (had0.trans h.symm)) hdv
    · exact absurd (mul_left_cancel (h.trans hb)).symm hav
    · exact absurd (mul_left_cancel (h.trans hc)).symm hbv
    · exact absurd (mul_left_cancel (h.trans hd)).symm hcv
    · exact h
    · exact absurd (eq_of_mul_eq_self_of_card_eq_six hM h) hav
  -- no element is a left unit for $a$
  have hno : ∀ x : M, x * a ≠ a := by
    intro x hx
    have hxc : x = c := by
      have h' := eq_cube_of_mul_eq hx
      rw [← hb, hba] at h'
      exact h'
    have h255 : Eq255At a := by
      change a * a * a * a = a
      rw [← hb, hba, ← hxc]
      exact hx
    have h4 : a * (a * a) = a * a * a := by rw [← hb, hc.symm, hba]
    exact hnid (isIdempotentElem_of_mul_sq_eq_sq_mul h255 h4)
  rcases hspan (d * a) with hcs1 | hcs1 | hcs1 | hcs1 | hcs1 | hcs1
  · -- $d \diamond a = a$
    exact absurd hcs1 (hno _)
  · -- $d \diamond a = b$
    have e1 : d * a = a * a := hcs1.trans hb.symm.symm
    have e2 : d * (a * a) = a * (a * a) := by
      rw [hb.symm]
      exact hdb.trans hc.symm.symm
    exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (had.symm)
  · -- $d \diamond a = c$
    exact absurd (mul_left_cancel (hcs1.trans hdb.symm)) hab
  · -- $d \diamond a = d$
    have hv2 : c * d = b :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
        ((congrArg (· * a) hd.symm).trans hcs1))).symm.trans
        (eq677 c a)).trans hc.symm.symm)
    rcases hspan (c * a) with hcs3 | hcs3 | hcs3 | hcs3 | hcs3 | hcs3
    · -- $c \diamond a = a$
      exact absurd hcs3 (hno _)
    · -- $c \diamond a = b$
      exact absurd (mul_left_cancel (hcs3.trans hv2.symm)) had
    · -- $c \diamond a = c$
      have hv4 : b * c = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs3))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv5 : c * b = b :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv4.symm)).trans hc.symm.symm)
      exact absurd (mul_left_cancel (hv5.trans hv2.symm)) hbd
    · -- $c \diamond a = d$
      have hv6 : b * d = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs3))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv7 : c * b = c :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv6.symm)).trans hd.symm.symm)
      rcases hspan (c * c) with hcs8 | hcs8 | hcs8 | hcs8 | hcs8 | hcs8
      · -- $c \diamond c = a$
        have hv9 : d * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
            (eq677 a c)).trans hcs8.symm)).trans hc.symm.symm)
        have hv10 : c * c = b :=
          (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv7).trans
            hcs8)).trans hba)).symm.trans (eq677 b c)
        exact absurd (hv10.symm.trans hcs8) (hab.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs8.trans hv2.symm)) hcd
      · -- $c \diamond c = c$
        exact absurd (mul_left_cancel (hcs8.trans hv7.symm)) (hbc.symm)
      · -- $c \diamond c = d$
        exact absurd (mul_left_cancel (hcs8.trans hcs3.symm)) (hac.symm)
      · -- $c \diamond c = u$
        have hv11 : b * u = d :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv7).trans hcs8))).symm.trans
            (eq677 b c)).trans hv2.symm)
        have hv12 : u * c = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (c * ·) (congrArg (· * c) hcs8))).symm.trans
            (eq677 c c)).trans hv7.symm)).trans hv2.symm)
        have hv13 : d * c = u :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
            ((congrArg (· * b) hv6).trans hc.symm))).symm.trans
            (eq677 d b)).trans hv11.symm)
        have hv14 : b * d = u :=
          (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv11).trans
            hdb)).trans hv12)).symm.trans (eq677 u b)
        exact absurd (hv14.symm.trans hv6) (hau.symm)
      · -- $c \diamond c = v$
        have hv15 : b * v = d :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv7).trans hcs8))).symm.trans
            (eq677 b c)).trans hv2.symm)
        have hv16 : v * c = d :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (c * ·) (congrArg (· * c) hcs8))).symm.trans
            (eq677 c c)).trans hv7.symm)).trans hv2.symm)
        have hv17 : d * c = v :=
          mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
            ((congrArg (· * b) hv6).trans hc.symm))).symm.trans
            (eq677 d b)).trans hv15.symm)
        have hv18 : b * d = v :=
          (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv15).trans
            hdb)).trans hv16)).symm.trans (eq677 v b)
        exact absurd (hv18.symm.trans hv6) (hav.symm)
    · -- $c \diamond a = u$
      have hv19 : b * u = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs3))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv20 : c * b = v :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv19.symm)).trans havu.symm)
      rcases hspan (c * c) with hcs21 | hcs21 | hcs21 | hcs21 | hcs21 | hcs21
      · -- $c \diamond c = a$
        have hv22 : u * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
            (eq677 a c)).trans hcs21.symm)).trans hc.symm.symm)
        have hv23 : c * b = c :=
          (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs21).trans
            hd.symm)).trans hv2)).symm.trans (eq677 c c)
        exact absurd (hv23.symm.trans hv20) hcv
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs21.trans hv2.symm)) hcd
      · -- $c \diamond c = c$
        rcases hspan (c * u) with hcs24 | hcs24 | hcs24 | hcs24 | hcs24 | hcs24
        · -- $c \diamond u = a$
          have hv25 : u * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hcs24.symm)).trans havu.symm)
          have hv26 : u * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs24).trans hd.symm))).symm.trans
              (eq677 u c)).trans hcs3.symm)
          have hv27 : c * v = d := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact absurd (mul_left_cancel (hz.trans hcs24.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs21.symm)) (hcv.symm)
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
            · exact absurd (mul_left_cancel (hz.trans hv20.symm)) (hbv.symm)
          have hv28 : v * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (u * ·) (congrArg (· * a) hauv))).symm.trans
              (eq677 u a)).trans havu.symm)).trans hv25.symm)
          have hv29 : b * v = u :=
            (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv19).trans
              hc.symm)).trans hv25)).symm.trans (eq677 u b)
          have hv30 : v * a = a :=
            (congrArg (v * ·) ((congrArg (a * ·) ((congrArg (· * v) hv28).trans
              hv27)).trans had0)).symm.trans (eq677 a v)
          exact absurd (hv30.symm.trans hv28) hac
        · -- $c \diamond u = b$
          exact absurd (mul_left_cancel (hcs24.trans hv2.symm)) (hdu.symm)
        · -- $c \diamond u = c$
          exact absurd (mul_left_cancel (hcs24.trans hcs21.symm)) (hcu.symm)
        · -- $c \diamond u = d$
          have hv31 : c * v = a := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs21.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs24.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
            · exact absurd (mul_left_cancel (hz.trans hv20.symm)) (hbv.symm)
          have hv32 : u * c = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hv31.symm)).trans hauv.symm)
          have hv33 : v * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (v * ·)
              ((congrArg (· * c) hv31).trans hd.symm))).symm.trans
              (eq677 v c)).trans hv20.symm)
          have hv34 : b * u = u :=
            (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv19).trans
              hc.symm)).trans hv32)).symm.trans (eq677 u b)
          exact absurd (hv34.symm.trans hv19) (hau.symm)
        · -- $c \diamond u = u$
          exact absurd (mul_left_cancel (hcs24.trans hcs3.symm)) (hau.symm)
        · -- $c \diamond u = v$
          exact absurd (mul_left_cancel (hcs24.trans hv20.symm)) (hbu.symm)
      · -- $c \diamond c = d$
        have hv35 : b * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (d * ·) (congrArg (· * c) hv2))).symm.trans
            (eq677 d c)).trans hcs21.symm)).trans hdb.symm)
        rcases hspan (c * u) with hcs36 | hcs36 | hcs36 | hcs36 | hcs36 | hcs36
        · -- $c \diamond u = a$
          have hv37 : b * b = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (c * ·) (congrArg (· * b) hv35))).symm.trans
              (eq677 c b)).trans hba.symm)).trans hcs36.symm)
          have hv38 : u * c = b :=
            mul_left_cancel (((congrArg (b * ·) (congrArg (u * ·)
              ((congrArg (· * b) hv19).trans hc.symm))).symm.trans
              (eq677 u b)).trans hv37.symm)
          have hv39 : c * c = a :=
            (congrArg (c * ·) ((congrArg (a * ·) ((congrArg (· * c) hcs3).trans
              hv38)).trans hc.symm)).symm.trans (eq677 a c)
          exact absurd (hv39.symm.trans hcs21) had
        · -- $c \diamond u = b$
          exact absurd (mul_left_cancel (hcs36.trans hv2.symm)) (hdu.symm)
        · -- $c \diamond u = c$
          have hv40 : d * c = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (c * ·) (congrArg (· * c) hcs21))).symm.trans
              (eq677 c c)).trans hcs36.symm)).trans hcs3.symm)
          have hv41 : u * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs36).trans hcs21))).symm.trans
              (eq677 u c)).trans hcs3.symm)
          have hv42 : d * d = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
              (congrArg (a * ·) (congrArg (· * d) hcs1))).symm.trans
              (eq677 a d)).trans hv40.symm)).trans hc.symm.symm)
          have hv43 : b * b = d :=
            mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
              ((congrArg (· * d) hdb).trans hv2))).symm.trans
              (eq677 b d)).trans hv42.symm)
          have e : b * b * (b * b) = b := by rw [hv43]; exact hv42
          exact absurd ((isIdempotentElem_of_sq_mul_sq e).eq.symm.trans hv43) hbd
        · -- $c \diamond u = d$
          exact absurd (mul_left_cancel (hcs36.trans hcs21.symm)) (hcu.symm)
        · -- $c \diamond u = u$
          exact absurd (mul_left_cancel (hcs36.trans hcs3.symm)) (hau.symm)
        · -- $c \diamond u = v$
          exact absurd (mul_left_cancel (hcs36.trans hv20.symm)) (hbu.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs21.trans hcs3.symm)) (hac.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs21.trans hv20.symm)) (hbc.symm)
    · -- $c \diamond a = v$
      have hv44 : b * v = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs3))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv45 : c * b = u :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv44.symm)).trans hauv.symm)
      rcases hspan (c * c) with hcs46 | hcs46 | hcs46 | hcs46 | hcs46 | hcs46
      · -- $c \diamond c = a$
        have hv47 : v * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
            (eq677 a c)).trans hcs46.symm)).trans hc.symm.symm)
        have hv48 : c * b = c :=
          (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs46).trans
            hd.symm)).trans hv2)).symm.trans (eq677 c c)
        exact absurd (hv48.symm.trans hv45) hcu
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs46.trans hv2.symm)) hcd
      · -- $c \diamond c = c$
        rcases hspan (c * u) with hcs49 | hcs49 | hcs49 | hcs49 | hcs49 | hcs49
        · -- $c \diamond u = a$
          have hv50 : v * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hcs49.symm)).trans havu.symm)
          have hv51 : u * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs49).trans hd.symm))).symm.trans
              (eq677 u c)).trans hv45.symm)
          have hv52 : c * v = d := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact absurd (mul_left_cancel (hz.trans hcs49.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs46.symm)) (hcv.symm)
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv45.symm)) (hbv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
          have hv53 : b * v = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv44).trans
              hc.symm)).trans hv50)).symm.trans (eq677 v b)
          exact absurd (hv53.symm.trans hv44) (hav.symm)
        · -- $c \diamond u = b$
          exact absurd (mul_left_cancel (hcs49.trans hv2.symm)) (hdu.symm)
        · -- $c \diamond u = c$
          exact absurd (mul_left_cancel (hcs49.trans hcs46.symm)) (hcu.symm)
        · -- $c \diamond u = d$
          have hv54 : c * v = a := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs46.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs49.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv45.symm)) (hbv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
          have hv55 : v * c = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hv54.symm)).trans hauv.symm)
          have hv56 : v * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (v * ·)
              ((congrArg (· * c) hv54).trans hd.symm))).symm.trans
              (eq677 v c)).trans hcs3.symm)
          have hv57 : u * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (v * ·) (congrArg (· * a) havu))).symm.trans
              (eq677 v a)).trans hauv.symm)).trans hv55.symm)
          have hv58 : b * u = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv44).trans
              hc.symm)).trans hv55)).symm.trans (eq677 v b)
          have hv59 : u * a = a :=
            (congrArg (u * ·) ((congrArg (a * ·) ((congrArg (· * u) hv57).trans
              hcs49)).trans had0)).symm.trans (eq677 a u)
          exact absurd (hv59.symm.trans hv57) hac
        · -- $c \diamond u = u$
          exact absurd (mul_left_cancel (hcs49.trans hv45.symm)) (hbu.symm)
        · -- $c \diamond u = v$
          exact absurd (mul_left_cancel (hcs49.trans hcs3.symm)) (hau.symm)
      · -- $c \diamond c = d$
        have hv60 : b * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (d * ·) (congrArg (· * c) hv2))).symm.trans
            (eq677 d c)).trans hcs46.symm)).trans hdb.symm)
        rcases hspan (c * u) with hcs61 | hcs61 | hcs61 | hcs61 | hcs61 | hcs61
        · -- $c \diamond u = a$
          have hv62 : b * b = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (c * ·) (congrArg (· * b) hv60))).symm.trans
              (eq677 c b)).trans hba.symm)).trans hcs61.symm)
          have hv63 : v * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs3))).symm.trans
              (eq677 a c)).trans hcs61.symm)).trans havu.symm)
          have hv64 : u * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs61).trans hd.symm))).symm.trans
              (eq677 u c)).trans hv45.symm)
          have hv65 : d * u = b :=
            (congrArg (d * ·) ((congrArg (b * ·) ((congrArg (· * d) hdb).trans
              hv2)).trans hv62)).symm.trans (eq677 b d)
          have hv66 : c * v = c := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact absurd (mul_left_cancel (hz.trans hcs61.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv2.symm)) (hdv.symm)
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hcs46.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv45.symm)) (hbv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) (hav.symm)
          have hv67 : u * b = a :=
            mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
              (congrArg (b * ·) (congrArg (· * b) hv62))).symm.trans
              (eq677 b b)).trans hv60.symm)).trans hba.symm)
          have hv68 : b * v = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv44).trans
              hc.symm)).trans hv63)).symm.trans (eq677 v b)
          exact absurd (hv68.symm.trans hv44) (hav.symm)
        · -- $c \diamond u = b$
          exact absurd (mul_left_cancel (hcs61.trans hv2.symm)) (hdu.symm)
        · -- $c \diamond u = c$
          have hv69 : d * c = b :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (c * ·) (congrArg (· * c) hcs46))).symm.trans
              (eq677 c c)).trans hcs61.symm)).trans hv45.symm)
          have hv70 : u * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hcs61).trans hcs46))).symm.trans
              (eq677 u c)).trans hv45.symm)
          have hv71 : b * b = c :=
            mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
              ((congrArg (· * d) hdb).trans hv2))).symm.trans
              (eq677 b d)).trans hv69.symm)
          exact absurd (mul_left_cancel (hv71.trans hba.symm)) (hab.symm)
        · -- $c \diamond u = d$
          exact absurd (mul_left_cancel (hcs61.trans hcs46.symm)) (hcu.symm)
        · -- $c \diamond u = u$
          exact absurd (mul_left_cancel (hcs61.trans hv45.symm)) (hbu.symm)
        · -- $c \diamond u = v$
          exact absurd (mul_left_cancel (hcs61.trans hcs3.symm)) (hau.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs46.trans hv45.symm)) (hbc.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs46.trans hcs3.symm)) (hac.symm)
  · -- $d \diamond a = u$
    have hv72 : c * u = b :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
        ((congrArg (· * a) hd.symm).trans hcs1))).symm.trans
        (eq677 c a)).trans hc.symm.symm)
    rcases hspan (c * a) with hcs73 | hcs73 | hcs73 | hcs73 | hcs73 | hcs73
    · -- $c \diamond a = a$
      exact absurd hcs73 (hno _)
    · -- $c \diamond a = b$
      exact absurd (mul_left_cancel (hcs73.trans hv72.symm)) hau
    · -- $c \diamond a = c$
      have hv74 : b * c = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv75 : c * b = b :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv74.symm)).trans hc.symm.symm)
      exact absurd (mul_left_cancel (hv75.trans hv72.symm)) hbu
    · -- $c \diamond a = d$
      have hv76 : b * d = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv77 : c * b = c :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv76.symm)).trans hd.symm.symm)
      rcases hspan (c * c) with hcs78 | hcs78 | hcs78 | hcs78 | hcs78 | hcs78
      · -- $c \diamond c = a$
        have hv79 : d * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
            (eq677 a c)).trans hcs78.symm)).trans hc.symm.symm)
        have hv80 : c * c = b :=
          (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv77).trans
            hcs78)).trans hba)).symm.trans (eq677 b c)
        exact absurd (hv80.symm.trans hcs78) (hab.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs78.trans hv72.symm)) hcu
      · -- $c \diamond c = c$
        exact absurd (mul_left_cancel (hcs78.trans hv77.symm)) (hbc.symm)
      · -- $c \diamond c = d$
        exact absurd (mul_left_cancel (hcs78.trans hcs73.symm)) (hac.symm)
      · -- $c \diamond c = u$
        have e : c * (c * (c * c)) = c := by rw [hcs78, hv72]; exact hv77
        exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hcs78) hcu
      · -- $c \diamond c = v$
        have hv81 : b * v = u :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv77).trans hcs78))).symm.trans
            (eq677 b c)).trans hv72.symm)
        have hv82 : v * c = u :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (c * ·) (congrArg (· * c) hcs78))).symm.trans
            (eq677 c c)).trans hv77.symm)).trans hv72.symm)
        have hv83 : u * a = c :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (v * ·) (congrArg (· * a) havu))).symm.trans
            (eq677 v a)).trans hauv.symm)).trans hv82.symm)
        have hv84 : u * c = a :=
          (congrArg (u * ·) ((congrArg (a * ·) ((congrArg (· * u) hv83).trans
            hv72)).trans hc.symm)).symm.trans (eq677 a u)
        have hv85 : c * v = a :=
          mul_left_cancel (((congrArg (u * ·) (congrArg (c * ·)
            ((congrArg (· * u) hv84).trans hauv))).symm.trans
            (eq677 c u)).trans hv83.symm)
        have hv86 : c * d = u := by
          rcases hspan (c * d) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans hv85.symm)) hdv
          · exact absurd (mul_left_cancel (hz.trans hv72.symm)) hdu
          · exact absurd (mul_left_cancel (hz.trans hv77.symm)) (hbd.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs73.symm)) (had.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs78.symm)) (hcd.symm)
        have hv87 : d * c = u :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
            (eq677 a c)).trans hv85.symm)).trans hauv.symm)
        exact absurd (mul_left_cancel (hv87.trans hcs1.symm)) (hac.symm)
    · -- $c \diamond a = u$
      have hv88 : b * u = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv89 : c * b = v :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv88.symm)).trans havu.symm)
      rcases hspan (c * c) with hcs90 | hcs90 | hcs90 | hcs90 | hcs90 | hcs90
      · -- $c \diamond c = a$
        have hv91 : u * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
            (eq677 a c)).trans hcs90.symm)).trans hc.symm.symm)
        have hv92 : u * u = c :=
          (congrArg (u * ·) ((congrArg (c * ·) ((congrArg (· * u) hv91).trans
            hv88)).trans hcs73)).symm.trans (eq677 c u)
        have hv93 : b * b = u :=
          (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv88).trans
            hc.symm)).trans hv91)).symm.trans (eq677 u b)
        have hv94 : v * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (b * ·) (congrArg (· * c) hv89))).symm.trans
            (eq677 b c)).trans hv72.symm)).trans hv93.symm)
        rcases hspan (c * d) with hcs95 | hcs95 | hcs95 | hcs95 | hcs95 | hcs95
        · -- $c \diamond d = a$
          exact absurd (mul_left_cancel (hcs95.trans hcs90.symm)) (hcd.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs95.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          have hv96 : c * c = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs90).trans
              hd.symm)).trans hcs95)).symm.trans (eq677 c c)
          exact absurd (hv96.symm.trans hcs90) (hac.symm)
        · -- $c \diamond d = d$
          have hv97 : c * d = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs90).trans
              hd.symm)).trans hcs95)).symm.trans (eq677 c c)
          exact absurd (hv97.symm.trans hcs95) hcd
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs95.trans hcs73.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs95.trans hv89.symm)) (hbd.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs90.trans hv72.symm)) hcu
      · -- $c \diamond c = c$
        rcases hspan (c * d) with hcs98 | hcs98 | hcs98 | hcs98 | hcs98 | hcs98
        · -- $c \diamond d = a$
          have hv99 : u * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
              (eq677 a c)).trans hcs98.symm)).trans hd.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs90).trans (eq_cube_of_mul_eq hv99).symm) hcu
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs98.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          exact absurd (mul_left_cancel (hcs98.trans hcs90.symm)) (hcd.symm)
        · -- $c \diamond d = d$
          have hv100 : c * v = a := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv72.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs90.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs98.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs73.symm)) (hav.symm)
            · exact absurd (mul_left_cancel (hz.trans hv89.symm)) (hbv.symm)
          have hv101 : u * c = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
              (eq677 a c)).trans hv100.symm)).trans hauv.symm)
          have hv102 : v * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (v * ·)
              ((congrArg (· * c) hv100).trans hd.symm))).symm.trans
              (eq677 v c)).trans hv89.symm)
          have hv103 : b * u = u :=
            (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv88).trans
              hc.symm)).trans hv101)).symm.trans (eq677 u b)
          exact absurd (hv103.symm.trans hv88) (hau.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs98.trans hcs73.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs98.trans hv89.symm)) (hbd.symm)
      · -- $c \diamond c = d$
        rcases hspan (c * d) with hcs104 | hcs104 | hcs104 | hcs104 | hcs104 | hcs104
        · -- $c \diamond d = a$
          have e1 : c * c = a * c := hcs90.trans hd.symm.symm
          have e2 : c * (a * c) = a * (a * c) := by
            rw [hd.symm]
            exact hcs104.trans had0.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hac.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs104.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          have e : c * (c * c) = c := by rw [hcs90]; exact hcs104
          exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs90) hcd
        · -- $c \diamond d = d$
          exact absurd (mul_left_cancel (hcs104.trans hcs90.symm)) (hcd.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs104.trans hcs73.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs104.trans hv89.symm)) (hbd.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs90.trans hcs73.symm)) (hac.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs90.trans hv89.symm)) (hbc.symm)
    · -- $c \diamond a = v$
      have hv105 : b * v = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv106 : c * b = u :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv105.symm)).trans hauv.symm)
      rcases hspan (c * c) with hcs107 | hcs107 | hcs107 | hcs107 | hcs107 | hcs107
      · -- $c \diamond c = a$
        have hv108 : v * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
            (eq677 a c)).trans hcs107.symm)).trans hc.symm.symm)
        have hv109 : v * v = c :=
          (congrArg (v * ·) ((congrArg (c * ·) ((congrArg (· * v) hv108).trans
            hv105)).trans hcs73)).symm.trans (eq677 c v)
        have hv110 : b * b = v :=
          (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv105).trans
            hc.symm)).trans hv108)).symm.trans (eq677 v b)
        rcases hspan (c * d) with hcs111 | hcs111 | hcs111 | hcs111 | hcs111 | hcs111
        · -- $c \diamond d = a$
          exact absurd (mul_left_cancel (hcs111.trans hcs107.symm)) (hcd.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs111.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          have hv112 : c * c = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs107).trans
              hd.symm)).trans hcs111)).symm.trans (eq677 c c)
          exact absurd (hv112.symm.trans hcs107) (hac.symm)
        · -- $c \diamond d = d$
          have hv113 : c * d = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs107).trans
              hd.symm)).trans hcs111)).symm.trans (eq677 c c)
          exact absurd (hv113.symm.trans hcs111) hcd
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs111.trans hv106.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs111.trans hcs73.symm)) (had.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs107.trans hv72.symm)) hcu
      · -- $c \diamond c = c$
        rcases hspan (c * d) with hcs114 | hcs114 | hcs114 | hcs114 | hcs114 | hcs114
        · -- $c \diamond d = a$
          have hv115 : v * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
              (eq677 a c)).trans hcs114.symm)).trans hd.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs107).trans (eq_cube_of_mul_eq hv115).symm) hcv
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs114.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          exact absurd (mul_left_cancel (hcs114.trans hcs107.symm)) (hcd.symm)
        · -- $c \diamond d = d$
          have hv116 : c * v = a := by
            rcases hspan (c * v) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv72.symm)) (huv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs107.symm)) (hcv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs114.symm)) (hdv.symm)
            · exact absurd (mul_left_cancel (hz.trans hv106.symm)) (hbv.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs73.symm)) (hav.symm)
          have hv117 : v * c = u :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs73))).symm.trans
              (eq677 a c)).trans hv116.symm)).trans hauv.symm)
          have hv118 : v * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (v * ·)
              ((congrArg (· * c) hv116).trans hd.symm))).symm.trans
              (eq677 v c)).trans hcs73.symm)
          have hv119 : u * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (v * ·) (congrArg (· * a) havu))).symm.trans
              (eq677 v a)).trans hauv.symm)).trans hv117.symm)
          have hv120 : b * u = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv105).trans
              hc.symm)).trans hv117)).symm.trans (eq677 v b)
          have hv121 : u * c = a :=
            (congrArg (u * ·) ((congrArg (a * ·) ((congrArg (· * u) hv119).trans
              hv72)).trans hc.symm)).symm.trans (eq677 a u)
          have hv122 : c * c = b :=
            (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv106).trans
              hv121)).trans hba)).symm.trans (eq677 b c)
          exact absurd (hv122.symm.trans hcs107) hbc
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs114.trans hv106.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs114.trans hcs73.symm)) (had.symm)
      · -- $c \diamond c = d$
        rcases hspan (c * d) with hcs123 | hcs123 | hcs123 | hcs123 | hcs123 | hcs123
        · -- $c \diamond d = a$
          have e1 : c * c = a * c := hcs107.trans hd.symm.symm
          have e2 : c * (a * c) = a * (a * c) := by
            rw [hd.symm]
            exact hcs123.trans had0.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hac.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs123.trans hv72.symm)) hdu
        · -- $c \diamond d = c$
          have e : c * (c * c) = c := by rw [hcs107]; exact hcs123
          exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs107) hcd
        · -- $c \diamond d = d$
          exact absurd (mul_left_cancel (hcs123.trans hcs107.symm)) (hcd.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs123.trans hv106.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs123.trans hcs73.symm)) (had.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs107.trans hv106.symm)) (hbc.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs107.trans hcs73.symm)) (hac.symm)
  · -- $d \diamond a = v$
    have hv124 : c * v = b :=
      mul_left_cancel (((congrArg (a * ·) (congrArg (c * ·)
        ((congrArg (· * a) hd.symm).trans hcs1))).symm.trans
        (eq677 c a)).trans hc.symm.symm)
    rcases hspan (c * a) with hcs125 | hcs125 | hcs125 | hcs125 | hcs125 | hcs125
    · -- $c \diamond a = a$
      exact absurd hcs125 (hno _)
    · -- $c \diamond a = b$
      exact absurd (mul_left_cancel (hcs125.trans hv124.symm)) hav
    · -- $c \diamond a = c$
      have hv126 : b * c = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs125))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv127 : c * b = b :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv126.symm)).trans hc.symm.symm)
      exact absurd (mul_left_cancel (hv127.trans hv124.symm)) hbv
    · -- $c \diamond a = d$
      have hv128 : b * d = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs125))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv129 : c * b = c :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv128.symm)).trans hd.symm.symm)
      rcases hspan (c * c) with hcs130 | hcs130 | hcs130 | hcs130 | hcs130 | hcs130
      · -- $c \diamond c = a$
        have hv131 : d * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
            (eq677 a c)).trans hcs130.symm)).trans hc.symm.symm)
        have hv132 : c * c = b :=
          (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv129).trans
            hcs130)).trans hba)).symm.trans (eq677 b c)
        exact absurd (hv132.symm.trans hcs130) (hab.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs130.trans hv124.symm)) hcv
      · -- $c \diamond c = c$
        exact absurd (mul_left_cancel (hcs130.trans hv129.symm)) (hbc.symm)
      · -- $c \diamond c = d$
        exact absurd (mul_left_cancel (hcs130.trans hcs125.symm)) (hac.symm)
      · -- $c \diamond c = u$
        have hv133 : b * u = v :=
          mul_left_cancel (((congrArg (c * ·) (congrArg (b * ·)
            ((congrArg (· * c) hv129).trans hcs130))).symm.trans
            (eq677 b c)).trans hv124.symm)
        have hv134 : u * c = v :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (c * ·) (congrArg (· * c) hcs130))).symm.trans
            (eq677 c c)).trans hv129.symm)).trans hv124.symm)
        have hv135 : v * a = c :=
          mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
            (congrArg (u * ·) (congrArg (· * a) hauv))).symm.trans
            (eq677 u a)).trans havu.symm)).trans hv134.symm)
        have hv136 : v * c = a :=
          (congrArg (v * ·) ((congrArg (a * ·) ((congrArg (· * v) hv135).trans
            hv124)).trans hc.symm)).symm.trans (eq677 a v)
        have hv137 : c * u = a :=
          mul_left_cancel (((congrArg (v * ·) (congrArg (c * ·)
            ((congrArg (· * v) hv136).trans havu))).symm.trans
            (eq677 c v)).trans hv135.symm)
        have hv138 : c * d = v := by
          rcases hspan (c * d) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans hv137.symm)) hdu
          · exact absurd (mul_left_cancel (hz.trans hv124.symm)) hdv
          · exact absurd (mul_left_cancel (hz.trans hv129.symm)) (hbd.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs125.symm)) (had.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (hcd.symm)
          · exact hz
        have hv139 : d * c = v :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
            (eq677 a c)).trans hv137.symm)).trans havu.symm)
        exact absurd (mul_left_cancel (hv139.trans hcs1.symm)) (hac.symm)
      · -- $c \diamond c = v$
        have e : c * (c * (c * c)) = c := by rw [hcs130, hv124]; exact hv129
        exact absurd ((isIdempotentElem_of_mul_mul_sq e).eq.symm.trans hcs130) hcv
    · -- $c \diamond a = u$
      have hv140 : b * u = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs125))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv141 : c * b = v :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv140.symm)).trans havu.symm)
      rcases hspan (c * c) with hcs142 | hcs142 | hcs142 | hcs142 | hcs142 | hcs142
      · -- $c \diamond c = a$
        have hv143 : u * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
            (eq677 a c)).trans hcs142.symm)).trans hc.symm.symm)
        have hv144 : u * u = c :=
          (congrArg (u * ·) ((congrArg (c * ·) ((congrArg (· * u) hv143).trans
            hv140)).trans hcs125)).symm.trans (eq677 c u)
        have hv145 : b * b = u :=
          (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv140).trans
            hc.symm)).trans hv143)).symm.trans (eq677 u b)
        rcases hspan (c * d) with hcs146 | hcs146 | hcs146 | hcs146 | hcs146 | hcs146
        · -- $c \diamond d = a$
          exact absurd (mul_left_cancel (hcs146.trans hcs142.symm)) (hcd.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs146.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          have hv147 : c * c = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs142).trans
              hd.symm)).trans hcs146)).symm.trans (eq677 c c)
          exact absurd (hv147.symm.trans hcs142) (hac.symm)
        · -- $c \diamond d = d$
          have hv148 : c * d = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs142).trans
              hd.symm)).trans hcs146)).symm.trans (eq677 c c)
          exact absurd (hv148.symm.trans hcs146) hcd
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs146.trans hcs125.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs146.trans hv141.symm)) (hbd.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs142.trans hv124.symm)) hcv
      · -- $c \diamond c = c$
        rcases hspan (c * d) with hcs149 | hcs149 | hcs149 | hcs149 | hcs149 | hcs149
        · -- $c \diamond d = a$
          have hv150 : u * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
              (eq677 a c)).trans hcs149.symm)).trans hd.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs142).trans (eq_cube_of_mul_eq hv150).symm) hcu
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs149.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          exact absurd (mul_left_cancel (hcs149.trans hcs142.symm)) (hcd.symm)
        · -- $c \diamond d = d$
          have hv151 : c * u = a := by
            rcases hspan (c * u) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv124.symm)) huv
            · exact absurd (mul_left_cancel (hz.trans hcs142.symm)) (hcu.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs149.symm)) (hdu.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs125.symm)) (hau.symm)
            · exact absurd (mul_left_cancel (hz.trans hv141.symm)) (hbu.symm)
          have hv152 : u * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
              (eq677 a c)).trans hv151.symm)).trans havu.symm)
          have hv153 : u * d = a :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hv151).trans hd.symm))).symm.trans
              (eq677 u c)).trans hcs125.symm)
          have hv154 : v * a = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
              (congrArg (u * ·) (congrArg (· * a) hauv))).symm.trans
              (eq677 u a)).trans havu.symm)).trans hv152.symm)
          have hv155 : b * v = u :=
            (congrArg (b * ·) ((congrArg (u * ·) ((congrArg (· * b) hv140).trans
              hc.symm)).trans hv152)).symm.trans (eq677 u b)
          have hv156 : v * c = a :=
            (congrArg (v * ·) ((congrArg (a * ·) ((congrArg (· * v) hv154).trans
              hv124)).trans hc.symm)).symm.trans (eq677 a v)
          have hv157 : c * c = b :=
            (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv141).trans
              hv156)).trans hba)).symm.trans (eq677 b c)
          exact absurd (hv157.symm.trans hcs142) hbc
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs149.trans hcs125.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs149.trans hv141.symm)) (hbd.symm)
      · -- $c \diamond c = d$
        rcases hspan (c * d) with hcs158 | hcs158 | hcs158 | hcs158 | hcs158 | hcs158
        · -- $c \diamond d = a$
          have e1 : c * c = a * c := hcs142.trans hd.symm.symm
          have e2 : c * (a * c) = a * (a * c) := by
            rw [hd.symm]
            exact hcs158.trans had0.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hac.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs158.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          have e : c * (c * c) = c := by rw [hcs142]; exact hcs158
          exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs142) hcd
        · -- $c \diamond d = d$
          exact absurd (mul_left_cancel (hcs158.trans hcs142.symm)) (hcd.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs158.trans hcs125.symm)) (had.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs158.trans hv141.symm)) (hbd.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs142.trans hcs125.symm)) (hac.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs142.trans hv141.symm)) (hbc.symm)
    · -- $c \diamond a = v$
      have hv159 : b * v = a :=
        mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
          ((congrArg (· * a) hc.symm).trans hcs125))).symm.trans
          (eq677 b a)).trans hb.symm.symm)
      have hv160 : c * b = u :=
        mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
          (congrArg (a * ·) (congrArg (· * b) hba))).symm.trans
          (eq677 a b)).trans hv159.symm)).trans hauv.symm)
      rcases hspan (c * c) with hcs161 | hcs161 | hcs161 | hcs161 | hcs161 | hcs161
      · -- $c \diamond c = a$
        have hv162 : v * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
            (eq677 a c)).trans hcs161.symm)).trans hc.symm.symm)
        have hv163 : v * v = c :=
          (congrArg (v * ·) ((congrArg (c * ·) ((congrArg (· * v) hv162).trans
            hv159)).trans hcs125)).symm.trans (eq677 c v)
        have hv164 : b * b = v :=
          (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv159).trans
            hc.symm)).trans hv162)).symm.trans (eq677 v b)
        have hv165 : u * c = b :=
          mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
            (congrArg (b * ·) (congrArg (· * c) hv160))).symm.trans
            (eq677 b c)).trans hv124.symm)).trans hv164.symm)
        rcases hspan (c * d) with hcs166 | hcs166 | hcs166 | hcs166 | hcs166 | hcs166
        · -- $c \diamond d = a$
          exact absurd (mul_left_cancel (hcs166.trans hcs161.symm)) (hcd.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs166.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          have hv167 : c * c = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs161).trans
              hd.symm)).trans hcs166)).symm.trans (eq677 c c)
          exact absurd (hv167.symm.trans hcs161) (hac.symm)
        · -- $c \diamond d = d$
          have hv168 : c * d = c :=
            (congrArg (c * ·) ((congrArg (c * ·) ((congrArg (· * c) hcs161).trans
              hd.symm)).trans hcs166)).symm.trans (eq677 c c)
          exact absurd (hv168.symm.trans hcs166) hcd
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs166.trans hv160.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs166.trans hcs125.symm)) (had.symm)
      · -- $c \diamond c = b$
        exact absurd (mul_left_cancel (hcs161.trans hv124.symm)) hcv
      · -- $c \diamond c = c$
        rcases hspan (c * d) with hcs169 | hcs169 | hcs169 | hcs169 | hcs169 | hcs169
        · -- $c \diamond d = a$
          have hv170 : v * c = c :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
              (eq677 a c)).trans hcs169.symm)).trans hd.symm.symm)
          exact absurd ((eq_cube_of_mul_eq hcs161).trans (eq_cube_of_mul_eq hv170).symm) hcv
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs169.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          exact absurd (mul_left_cancel (hcs169.trans hcs161.symm)) (hcd.symm)
        · -- $c \diamond d = d$
          have hv171 : c * u = a := by
            rcases hspan (c * u) with hz | hz | hz | hz | hz | hz
            · exact hz
            · exact absurd (mul_left_cancel (hz.trans hv124.symm)) huv
            · exact absurd (mul_left_cancel (hz.trans hcs161.symm)) (hcu.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs169.symm)) (hdu.symm)
            · exact absurd (mul_left_cancel (hz.trans hv160.symm)) (hbu.symm)
            · exact absurd (mul_left_cancel (hz.trans hcs125.symm)) (hau.symm)
          have hv172 : v * c = v :=
            mul_left_cancel ((mul_left_cancel (((congrArg (c * ·)
              (congrArg (a * ·) (congrArg (· * c) hcs125))).symm.trans
              (eq677 a c)).trans hv171.symm)).trans havu.symm)
          have hv173 : u * d = b :=
            mul_left_cancel (((congrArg (c * ·) (congrArg (u * ·)
              ((congrArg (· * c) hv171).trans hd.symm))).symm.trans
              (eq677 u c)).trans hv160.symm)
          have hv174 : b * v = v :=
            (congrArg (b * ·) ((congrArg (v * ·) ((congrArg (· * b) hv159).trans
              hc.symm)).trans hv172)).symm.trans (eq677 v b)
          exact absurd (hv174.symm.trans hv159) (hav.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs169.trans hv160.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs169.trans hcs125.symm)) (had.symm)
      · -- $c \diamond c = d$
        rcases hspan (c * d) with hcs175 | hcs175 | hcs175 | hcs175 | hcs175 | hcs175
        · -- $c \diamond d = a$
          have e1 : c * c = a * c := hcs161.trans hd.symm.symm
          have e2 : c * (a * c) = a * (a * c) := by
            rw [hd.symm]
            exact hcs175.trans had0.symm
          exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hac.symm)
        · -- $c \diamond d = b$
          exact absurd (mul_left_cancel (hcs175.trans hv124.symm)) hdv
        · -- $c \diamond d = c$
          have e : c * (c * c) = c := by rw [hcs161]; exact hcs175
          exact absurd ((isIdempotentElem_of_mul_sq e).eq.symm.trans hcs161) hcd
        · -- $c \diamond d = d$
          exact absurd (mul_left_cancel (hcs175.trans hcs161.symm)) (hcd.symm)
        · -- $c \diamond d = u$
          exact absurd (mul_left_cancel (hcs175.trans hv160.symm)) (hbd.symm)
        · -- $c \diamond d = v$
          exact absurd (mul_left_cancel (hcs175.trans hcs125.symm)) (had.symm)
      · -- $c \diamond c = u$
        exact absurd (mul_left_cancel (hcs161.trans hv160.symm)) (hbc.symm)
      · -- $c \diamond c = v$
        exact absurd (mul_left_cancel (hcs161.trans hcs125.symm)) (hac.symm)

/-- **At order six every element is idempotent.** A non-idempotent element has degree $4$, $5$ or
$6$ (degrees $2$ and $3$ never occur, and the degree is at most the order), and each is
excluded above. -/
theorem forall_isIdempotentElem_of_card_eq_six (hM : Finite.card M = 6) (a : M) :
    IsIdempotentElem a := by
  by_cases ha : IsIdempotentElem a
  · exact ha
  · obtain ⟨n, hn, hdeg⟩ := exists_hasDeg a
    rw [hM] at hn
    have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
      have := hdeg.1
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (ha hdeg.2.1).elim
    · exact absurd hdeg (not_hasDeg_two a)
    · exact absurd hdeg (not_hasDeg_three a)
    · exact absurd hdeg (not_hasDeg_four_of_card_eq_six hM a)
    · exact absurd hdeg (not_hasDeg_five_of_card_eq_six hM a)
    · exact absurd hdeg (not_hasDeg_six_of_card_eq_six hM a)

/-- **No six-element magma satisfies Equation 677 and the idempotent law.**

Under the idempotent law a product $x \diamond y$ with $x \neq y$ avoids both factors
(`eq_of_mul_eq_self_left`, `eq_of_mul_eq_self_right`) and both backward steps $x / y$ and
$x / y / y$ (`eq_of_mul_eq_div`, `eq_of_mul_eq_div_div`). Name two distinct elements $a, b$,
their product $c = a \diamond b$, and the remaining three elements $d, e, f$. The diagonal is
known, every other cell ranges over a handful of values, and a case analysis — each step an
instance of Equation 677, a left cancellation, one of the removals above, or the separation
lemma `eq_of_mul_eq_of_mul_mul_eq` — refutes every assignment. -/
theorem not_forall_isIdempotentElem_of_card_eq_six (hM : Finite.card M = 6)
    (hidem : ∀ x : M, IsIdempotentElem x) : False := by
  -- two distinct elements and their product
  obtain ⟨a, -⟩ := Finite.exists_notMem (l := ([] : List M))
    (by simp [hM])
  obtain ⟨b, hbm⟩ := Finite.exists_notMem (l := [a]) (by simp [hM])
  have hab : a ≠ b := fun h => hbm (by rw [h]; simp)
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  have hac : a ≠ c := by
    intro h
    have h' : a * b = a := by rw [← hc, ← h]
    exact hab (eq_of_mul_eq_self_left (hidem a) h').symm
  have hbc : b ≠ c := by
    intro h
    have h' : a * b = b := by rw [← hc, ← h]
    exact hab (eq_of_mul_eq_self_right (hidem b) h')
  -- the remaining three elements
  obtain ⟨d, hdm⟩ := Finite.exists_notMem (l := [a, b, c])
    (by simp [hM])
  obtain ⟨e, hem⟩ := Finite.exists_notMem (l := [a, b, c, d])
    (by simp [hM])
  obtain ⟨f, hfm⟩ := Finite.exists_notMem (l := [a, b, c, d, e])
    (by simp [hM])
  have had : a ≠ d := fun h => hdm (by rw [h]; simp)
  have hbd : b ≠ d := fun h => hdm (by rw [h]; simp)
  have hcd : c ≠ d := fun h => hdm (by rw [h]; simp)
  have hae : a ≠ e := fun h => hem (by rw [h]; simp)
  have hbe : b ≠ e := fun h => hem (by rw [h]; simp)
  have hce : c ≠ e := fun h => hem (by rw [h]; simp)
  have hde : d ≠ e := fun h => hem (by rw [h]; simp)
  have haf : a ≠ f := fun h => hfm (by rw [h]; simp)
  have hbf : b ≠ f := fun h => hfm (by rw [h]; simp)
  have hcf : c ≠ f := fun h => hfm (by rw [h]; simp)
  have hdf : d ≠ f := fun h => hfm (by rw [h]; simp)
  have hef : e ≠ f := fun h => hfm (by rw [h]; simp)
  -- the six elements exhaust the carrier
  have hspan : ∀ z : M, z = a ∨ z = b ∨ z = c ∨ z = d ∨ z = e ∨ z = f :=
    Finite.span_six hM hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef
  rcases hspan (a * d) with hcs1 | hcs1 | hcs1 | hcs1 | hcs1 | hcs1
  · -- $a \diamond d = a$
    exact absurd (mul_left_cancel (hcs1.trans (hidem a).eq.symm)) (had.symm)
  · -- $a \diamond d = b$
    rcases hspan (a * e) with hcs2 | hcs2 | hcs2 | hcs2 | hcs2 | hcs2
    · -- $a \diamond e = a$
      exact absurd (mul_left_cancel (hcs2.trans (hidem a).eq.symm)) (hae.symm)
    · -- $a \diamond e = b$
      exact absurd (mul_left_cancel (hcs2.trans hcs1.symm)) (hde.symm)
    · -- $a \diamond e = c$
      exact absurd (mul_left_cancel (hcs2.trans hc.symm.symm)) (hbe.symm)
    · -- $a \diamond e = d$
      rcases hspan (a * f) with hcs3 | hcs3 | hcs3 | hcs3 | hcs3 | hcs3
      · -- $a \diamond f = a$
        exact absurd (mul_left_cancel (hcs3.trans (hidem a).eq.symm)) (haf.symm)
      · -- $a \diamond f = b$
        exact absurd (mul_left_cancel (hcs3.trans hcs1.symm)) (hdf.symm)
      · -- $a \diamond f = c$
        exact absurd (mul_left_cancel (hcs3.trans hc.symm.symm)) (hbf.symm)
      · -- $a \diamond f = d$
        exact absurd (mul_left_cancel (hcs3.trans hcs2.symm)) (hef.symm)
      · -- $a \diamond f = e$
        have hv4 : a * c = f := by
          rcases hspan (a * c) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hac.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) hcd
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbc.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs2.symm)) hce
          · exact absurd (mul_left_cancel (hz.trans hcs3.symm)) hcf
          · exact hz
        rcases hspan (b * a) with hcs5 | hcs5 | hcs5 | hcs5 | hcs5 | hcs5
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs5) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs5.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv6 : d * c = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs5))).symm.trans
              (eq677 d a)).trans hcs2.symm)
          rcases hspan (c * a) with hcs7 | hcs7 | hcs7 | hcs7 | hcs7 | hcs7
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs7) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs7.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs7.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs7.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv8 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs7))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * f) with hcs9 | hcs9 | hcs9 | hcs9 | hcs9 | hcs9
            · -- $b \diamond f = a$
              have hv10 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                  (eq677 a b)).trans hcs9.symm)).trans hv4.symm)
              exact absurd (mul_left_cancel (hv10.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond f = b$
              exact absurd (mul_left_cancel (hcs9.trans (hidem b).eq.symm)) (hbf.symm)
            · -- $b \diamond f = c$
              exact absurd (mul_left_cancel (hcs9.trans hcs5.symm)) (haf.symm)
            · -- $b \diamond f = d$
              exact absurd (mul_left_cancel (hcs9.trans hv8.symm)) (hef.symm)
            · -- $b \diamond f = e$
              have e1 : b * f = a * f := hcs9.trans hcs3.symm
              have e2 : b * (a * f) = a * (a * f) := by
                rw [hcs3]
                exact hv8.trans hcs2.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
            · -- $b \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs9) hbf
          · -- $c \diamond a = f$
            have hv11 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs7))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * e) with hcs12 | hcs12 | hcs12 | hcs12 | hcs12 | hcs12
            · -- $b \diamond e = a$
              have hv13 : c * b = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                  (eq677 a b)).trans hcs12.symm)).trans hcs3.symm)
              exact absurd (mul_left_cancel (hv13.trans hcs7.symm)) (hab.symm)
            · -- $b \diamond e = b$
              exact absurd (mul_left_cancel (hcs12.trans (hidem b).eq.symm)) (hbe.symm)
            · -- $b \diamond e = c$
              exact absurd (mul_left_cancel (hcs12.trans hcs5.symm)) (hae.symm)
            · -- $b \diamond e = d$
              exact absurd (mul_left_cancel (hcs12.trans hv11.symm)) hef
            · -- $b \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs12) hbe
            · -- $b \diamond e = f$
              rcases hspan (b * c) with hcs14 | hcs14 | hcs14 | hcs14 | hcs14 | hcs14
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs14
                have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs14.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs14.trans hcs5.symm)) (hac.symm)
              · -- $b \diamond c = d$
                exact absurd (mul_left_cancel (hcs14.trans hv11.symm)) hcf
              · -- $b \diamond c = e$
                have hv15 : b * d = a := by
                  rcases hspan (b * d) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbd.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs5.symm)) (had.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv11.symm)) hdf
                  · exact absurd (mul_left_cancel (hz.trans hcs14.symm)) (hcd.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs12.symm)) hde
                have hv16 : c * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                    (eq677 a b)).trans hv15.symm)).trans hcs2.symm)
                have hv17 : b * e = d :=
                  (congrArg (b * ·) ((congrArg (d * ·) ((congrArg (· * b) hv15).trans
                    hc.symm)).trans hv6)).symm.trans (eq677 d b)
                exact absurd (hv17.symm.trans hcs12) hdf
              · -- $b \diamond c = f$
                exact absurd (mul_left_cancel (hcs14.trans hcs12.symm)) hce
        · -- $b \diamond a = d$
          have hdv : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hik : IsIdempotentElem (b / a) := hdv ▸ hidem d
          exact absurd (eq_of_mul_eq_div hik (hcs5.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hdv1 : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hdv2 : b / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs2
          have hik : IsIdempotentElem (b / a / a) := hdv2 ▸ hidem e
          exact absurd (eq_of_mul_eq_div_div hik (hcs5.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hv18 : d * f = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs5))).symm.trans
              (eq677 d a)).trans hcs2.symm)
          rcases hspan (c * a) with hcs19 | hcs19 | hcs19 | hcs19 | hcs19 | hcs19
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs19) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs19.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs19.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs19.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv20 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs19))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * c) with hcs21 | hcs21 | hcs21 | hcs21 | hcs21 | hcs21
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs21
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs21.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs21) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs21.trans hv20.symm)) hce
            · -- $b \diamond c = e$
              rcases hspan (b * d) with hcs22 | hcs22 | hcs22 | hcs22 | hcs22 | hcs22
              · -- $b \diamond d = a$
                have hv23 : f * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                    (eq677 a b)).trans hcs22.symm)).trans hcs2.symm)
                have hv24 : d * c = e :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs22).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hv20.symm)
                exact absurd (mul_left_cancel (hv24.trans hv18.symm)) hcf
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs22.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv25 : c * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (d * ·) (congrArg (· * b) hcs22))).symm.trans
                    (eq677 d b)).trans hv20.symm)).trans hv18.symm)
                have hv26 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs22.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv20.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs21.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs5.symm)) (haf.symm)
                have hv27 : f * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs5))).symm.trans
                    (eq677 a b)).trans hv26.symm)).trans hv4.symm)
                have hv28 : f * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv26).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hcs5.symm)
                have hv29 : c * f = b :=
                  (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv25).trans
                    hv28)).trans hcs5)).symm.trans (eq677 b c)
                have hdv : c / f = b := div_eq_iff_mul_eq.mpr hv27
                have hik : IsIdempotentElem (c / f) := hdv ▸ hidem b
                exact absurd (eq_of_mul_eq_div hik (hv29.trans hdv.symm)) hcf
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs22.trans hv20.symm)) hde
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs22.trans hcs21.symm)) (hcd.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs22.trans hcs5.symm)) (had.symm)
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs21.trans hcs5.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv30 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs19))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (d * b) with hcs31 | hcs31 | hcs31 | hcs31 | hcs31 | hcs31
            · -- $d \diamond b = a$
              have hdv1 : d / b = f := div_eq_iff_mul_eq.mpr hv30
              have hdv2 : d / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs5
              have hik : IsIdempotentElem (d / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs31.trans hdv2.symm)) (hbd.symm)
            · -- $d \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs31) (hbd.symm)
            · -- $d \diamond b = c$
              have hv32 : f * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                  ((congrArg (· * b) hv30).trans hcs31))).symm.trans
                  (eq677 f b)).trans hcs5.symm)
              have hdv : f / c = a := div_eq_iff_mul_eq.mpr hcs19
              have hik : IsIdempotentElem (f / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv32.trans hdv.symm)) (hcf.symm)
            · -- $d \diamond b = d$
              exact absurd (mul_left_cancel (hcs31.trans (hidem d).eq.symm)) hbd
            · -- $d \diamond b = e$
              exact absurd (mul_left_cancel (hcs31.trans hv18.symm)) hbf
            · -- $d \diamond b = f$
              have hdv : d / b = f := div_eq_iff_mul_eq.mpr hv30
              have hik : IsIdempotentElem (d / b) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs31.trans hdv.symm)) (hbd.symm)
      · -- $a \diamond f = f$
        exact absurd (eq_of_mul_eq_self_right (hidem f) hcs3) haf
    · -- $a \diamond e = e$
      exact absurd (eq_of_mul_eq_self_right (hidem e) hcs2) hae
    · -- $a \diamond e = f$
      rcases hspan (a * c) with hcs33 | hcs33 | hcs33 | hcs33 | hcs33 | hcs33
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs33.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        exact absurd (mul_left_cancel (hcs33.trans hcs1.symm)) hcd
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs33.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        have hv34 : a * f = e := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs33.symm)) (hcf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs2.symm)) (hef.symm)
        rcases hspan (b * a) with hcs35 | hcs35 | hcs35 | hcs35 | hcs35 | hcs35
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs35) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs35.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hdv1 : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hdv2 : b / a / a = c := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs33
          have hik : IsIdempotentElem (b / a / a) := hdv2 ▸ hidem c
          exact absurd (eq_of_mul_eq_div_div hik (hcs35.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = d$
          have hdv : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hik : IsIdempotentElem (b / a) := hdv ▸ hidem d
          exact absurd (eq_of_mul_eq_div hik (hcs35.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hv36 : d * e = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs35))).symm.trans
              (eq677 d a)).trans hcs33.symm)
          rcases hspan (c * a) with hcs37 | hcs37 | hcs37 | hcs37 | hcs37 | hcs37
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs37) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs37.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs37.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs37.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv38 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs37))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (d * b) with hcs39 | hcs39 | hcs39 | hcs39 | hcs39 | hcs39
            · -- $d \diamond b = a$
              have hdv1 : d / b = e := div_eq_iff_mul_eq.mpr hv38
              have hdv2 : d / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs35
              have hik : IsIdempotentElem (d / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs39.trans hdv2.symm)) (hbd.symm)
            · -- $d \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs39) (hbd.symm)
            · -- $d \diamond b = c$
              exact absurd (mul_left_cancel (hcs39.trans hv36.symm)) hbe
            · -- $d \diamond b = d$
              exact absurd (mul_left_cancel (hcs39.trans (hidem d).eq.symm)) hbd
            · -- $d \diamond b = e$
              have hdv : d / b = e := div_eq_iff_mul_eq.mpr hv38
              have hik : IsIdempotentElem (d / b) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs39.trans hdv.symm)) (hbd.symm)
            · -- $d \diamond b = f$
              have hv40 : e * f = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                  ((congrArg (· * b) hv38).trans hcs39))).symm.trans
                  (eq677 e b)).trans hcs35.symm)
              have hdv : a / e = f := div_eq_iff_mul_eq.mpr hv40
              have hik : IsIdempotentElem (a / e) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs2.trans hdv.symm)) hae
          · -- $c \diamond a = f$
            have hv41 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs37))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * c) with hcs42 | hcs42 | hcs42 | hcs42 | hcs42 | hcs42
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs42
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs42.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs42) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs42.trans hv41.symm)) hcf
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs42.trans hcs35.symm)) (hac.symm)
            · -- $b \diamond c = f$
              rcases hspan (b * d) with hcs43 | hcs43 | hcs43 | hcs43 | hcs43 | hcs43
              · -- $b \diamond d = a$
                have hv44 : e * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs35))).symm.trans
                    (eq677 a b)).trans hcs43.symm)).trans hcs33.symm)
                have hv45 : d * c = f :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs43).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hv41.symm)
                have hv46 : b * e = c := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs43.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hv41.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs35.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs42.symm)) (hce.symm)
                have e1 : d * e = b * e := hv36.trans hv46.symm
                have e2 : d * (b * e) = b * (b * e) := by
                  rw [hv46]
                  exact hv45.trans hcs42.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbd.symm)
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs43.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv47 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs43.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv41.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs35.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs42.symm)) (hce.symm)
                have hv48 : e * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs35))).symm.trans
                    (eq677 a b)).trans hv47.symm)).trans hv34.symm)
                have hv49 : e * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hv47).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hcs35.symm)
                have hv50 : f * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (e * ·) (congrArg (· * a) hcs2))).symm.trans
                    (eq677 e a)).trans hv34.symm)).trans hv48.symm)
                have hv51 : f * b = a :=
                  (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hv50).trans
                    hv41)).trans hcs1)).symm.trans (eq677 a f)
                have hv52 : b * f = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs42).trans
                    hv51)).trans hcs37)).symm.trans (eq677 c b)
                exact absurd (hv52.symm.trans hv41) hcd
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs43.trans hv41.symm)) hdf
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs43.trans hcs35.symm)) (had.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs43.trans hcs42.symm)) (hcd.symm)
        · -- $b \diamond a = f$
          have hv53 : d * f = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs35))).symm.trans
              (eq677 d a)).trans hcs33.symm)
          rcases hspan (c * a) with hcs54 | hcs54 | hcs54 | hcs54 | hcs54 | hcs54
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs54) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs54.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs54.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs54.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv55 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs54))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * c) with hcs56 | hcs56 | hcs56 | hcs56 | hcs56 | hcs56
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs56
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs56.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs56) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs56.trans hv55.symm)) hce
            · -- $b \diamond c = e$
              rcases hspan (b * d) with hcs57 | hcs57 | hcs57 | hcs57 | hcs57 | hcs57
              · -- $b \diamond d = a$
                have hv58 : f * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs35))).symm.trans
                    (eq677 a b)).trans hcs57.symm)).trans hcs33.symm)
                have hv59 : d * c = e :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs57).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hv55.symm)
                have hv60 : b * f = c := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs57.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hv55.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs56.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs35.symm)) (haf.symm)
                have e1 : d * f = b * f := hv53.trans hv60.symm
                have e2 : d * (b * f) = b * (b * f) := by
                  rw [hv60]
                  exact hv59.trans hcs56.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbd.symm)
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs57.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv61 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs57.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv55.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs56.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs35.symm)) (haf.symm)
                have hv62 : f * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs35))).symm.trans
                    (eq677 a b)).trans hv61.symm)).trans hcs2.symm)
                have hv63 : f * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv61).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hcs35.symm)
                have hv64 : e * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (f * ·) (congrArg (· * a) hv34))).symm.trans
                    (eq677 f a)).trans hcs2.symm)).trans hv62.symm)
                have hv65 : e * b = a :=
                  (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hv64).trans
                    hv55)).trans hcs1)).symm.trans (eq677 a e)
                have hv66 : b * e = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs56).trans
                    hv65)).trans hcs54)).symm.trans (eq677 c b)
                exact absurd (hv66.symm.trans hv55) hcd
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs57.trans hv55.symm)) hde
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs57.trans hcs56.symm)) (hcd.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs57.trans hcs35.symm)) (had.symm)
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs56.trans hcs35.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv67 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs54))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (d * b) with hcs68 | hcs68 | hcs68 | hcs68 | hcs68 | hcs68
            · -- $d \diamond b = a$
              have hdv1 : d / b = f := div_eq_iff_mul_eq.mpr hv67
              have hdv2 : d / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs35
              have hik : IsIdempotentElem (d / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs68.trans hdv2.symm)) (hbd.symm)
            · -- $d \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs68) (hbd.symm)
            · -- $d \diamond b = c$
              exact absurd (mul_left_cancel (hcs68.trans hv53.symm)) hbf
            · -- $d \diamond b = d$
              exact absurd (mul_left_cancel (hcs68.trans (hidem d).eq.symm)) hbd
            · -- $d \diamond b = e$
              have hv69 : f * e = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                  ((congrArg (· * b) hv67).trans hcs68))).symm.trans
                  (eq677 f b)).trans hcs35.symm)
              have hdv : a / f = e := div_eq_iff_mul_eq.mpr hv69
              have hik : IsIdempotentElem (a / f) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hv34.trans hdv.symm)) haf
            · -- $d \diamond b = f$
              have hdv : d / b = f := div_eq_iff_mul_eq.mpr hv67
              have hik : IsIdempotentElem (d / b) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs68.trans hdv.symm)) (hbd.symm)
      · -- $a \diamond c = e$
        have hv70 : a * f = d := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs33.symm)) (hcf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs2.symm)) (hef.symm)
        rcases hspan (b * a) with hcs71 | hcs71 | hcs71 | hcs71 | hcs71 | hcs71
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs71) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs71.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv72 : d * c = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs71))).symm.trans
              (eq677 d a)).trans hv70.symm)
          rcases hspan (c * a) with hcs73 | hcs73 | hcs73 | hcs73 | hcs73 | hcs73
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs73) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs73.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs73.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs73.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv74 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * f) with hcs75 | hcs75 | hcs75 | hcs75 | hcs75 | hcs75
            · -- $b \diamond f = a$
              have hv76 : c * b = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                  (eq677 a b)).trans hcs75.symm)).trans hcs2.symm)
              exact absurd (mul_left_cancel (hv76.trans hcs73.symm)) (hab.symm)
            · -- $b \diamond f = b$
              exact absurd (mul_left_cancel (hcs75.trans (hidem b).eq.symm)) (hbf.symm)
            · -- $b \diamond f = c$
              exact absurd (mul_left_cancel (hcs75.trans hcs71.symm)) (haf.symm)
            · -- $b \diamond f = d$
              exact absurd (mul_left_cancel (hcs75.trans hv74.symm)) (hef.symm)
            · -- $b \diamond f = e$
              rcases hspan (b * c) with hcs77 | hcs77 | hcs77 | hcs77 | hcs77 | hcs77
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs77
                have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs77.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs77.trans hcs71.symm)) (hac.symm)
              · -- $b \diamond c = d$
                exact absurd (mul_left_cancel (hcs77.trans hv74.symm)) hce
              · -- $b \diamond c = e$
                exact absurd (mul_left_cancel (hcs77.trans hcs75.symm)) hcf
              · -- $b \diamond c = f$
                have hv78 : b * d = a := by
                  rcases hspan (b * d) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbd.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs71.symm)) (had.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv74.symm)) hde
                  · exact absurd (mul_left_cancel (hz.trans hcs75.symm)) hdf
                  · exact absurd (mul_left_cancel (hz.trans hcs77.symm)) (hcd.symm)
                have hv79 : c * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                    (eq677 a b)).trans hv78.symm)).trans hv70.symm)
                have hv80 : b * f = d :=
                  (congrArg (b * ·) ((congrArg (d * ·) ((congrArg (· * b) hv78).trans
                    hc.symm)).trans hv72)).symm.trans (eq677 d b)
                exact absurd (hv80.symm.trans hcs75) hde
            · -- $b \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs75) hbf
          · -- $c \diamond a = f$
            have hv81 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs73))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * e) with hcs82 | hcs82 | hcs82 | hcs82 | hcs82 | hcs82
            · -- $b \diamond e = a$
              have hv83 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                  (eq677 a b)).trans hcs82.symm)).trans hcs33.symm)
              exact absurd (mul_left_cancel (hv83.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond e = b$
              exact absurd (mul_left_cancel (hcs82.trans (hidem b).eq.symm)) (hbe.symm)
            · -- $b \diamond e = c$
              exact absurd (mul_left_cancel (hcs82.trans hcs71.symm)) (hae.symm)
            · -- $b \diamond e = d$
              exact absurd (mul_left_cancel (hcs82.trans hv81.symm)) hef
            · -- $b \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs82) hbe
            · -- $b \diamond e = f$
              have e1 : b * e = a * e := hcs82.trans hcs2.symm
              have e2 : b * (a * e) = a * (a * e) := by
                rw [hcs2]
                exact hv81.trans hv70.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
        · -- $b \diamond a = d$
          have hdv : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hik : IsIdempotentElem (b / a) := hdv ▸ hidem d
          exact absurd (eq_of_mul_eq_div hik (hcs71.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hv84 : d * e = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
              ((congrArg (· * a) hcs1).trans hcs71))).symm.trans
              (eq677 d a)).trans hv70.symm)
          rcases hspan (c * a) with hcs85 | hcs85 | hcs85 | hcs85 | hcs85 | hcs85
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs85) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs85.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs85.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs85.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hv86 : b * e = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs85))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (d * b) with hcs87 | hcs87 | hcs87 | hcs87 | hcs87 | hcs87
            · -- $d \diamond b = a$
              have hdv1 : d / b = e := div_eq_iff_mul_eq.mpr hv86
              have hdv2 : d / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs71
              have hik : IsIdempotentElem (d / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs87.trans hdv2.symm)) (hbd.symm)
            · -- $d \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs87) (hbd.symm)
            · -- $d \diamond b = c$
              have hv88 : e * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                  ((congrArg (· * b) hv86).trans hcs87))).symm.trans
                  (eq677 e b)).trans hcs71.symm)
              have hdv : e / c = a := div_eq_iff_mul_eq.mpr hcs85
              have hik : IsIdempotentElem (e / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv88.trans hdv.symm)) (hce.symm)
            · -- $d \diamond b = d$
              exact absurd (mul_left_cancel (hcs87.trans (hidem d).eq.symm)) hbd
            · -- $d \diamond b = e$
              have hdv : d / b = e := div_eq_iff_mul_eq.mpr hv86
              have hik : IsIdempotentElem (d / b) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs87.trans hdv.symm)) (hbd.symm)
            · -- $d \diamond b = f$
              exact absurd (mul_left_cancel (hcs87.trans hv84.symm)) hbe
          · -- $c \diamond a = f$
            have hv89 : b * f = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs85))).symm.trans
                (eq677 b a)).trans hcs1.symm)
            rcases hspan (b * c) with hcs90 | hcs90 | hcs90 | hcs90 | hcs90 | hcs90
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs90
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs90.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs90) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs90.trans hv89.symm)) hcf
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs90.trans hcs71.symm)) (hac.symm)
            · -- $b \diamond c = f$
              rcases hspan (b * d) with hcs91 | hcs91 | hcs91 | hcs91 | hcs91 | hcs91
              · -- $b \diamond d = a$
                have hv92 : e * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                    (eq677 a b)).trans hcs91.symm)).trans hv70.symm)
                have hv93 : d * c = f :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs91).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hv89.symm)
                exact absurd (mul_left_cancel (hv93.trans hv84.symm)) hce
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs91.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv94 : c * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (d * ·) (congrArg (· * b) hcs91))).symm.trans
                    (eq677 d b)).trans hv89.symm)).trans hv84.symm)
                have hv95 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs91.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv89.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs71.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs90.symm)) (hce.symm)
                have hv96 : e * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs71))).symm.trans
                    (eq677 a b)).trans hv95.symm)).trans hcs33.symm)
                have hv97 : e * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hv95).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hcs71.symm)
                have hv98 : c * e = b :=
                  (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv94).trans
                    hv97)).trans hcs71)).symm.trans (eq677 b c)
                have hdv : c / e = b := div_eq_iff_mul_eq.mpr hv96
                have hik : IsIdempotentElem (c / e) := hdv ▸ hidem b
                exact absurd (eq_of_mul_eq_div hik (hv98.trans hdv.symm)) hce
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs91.trans hv89.symm)) hdf
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs91.trans hcs71.symm)) (had.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs91.trans hcs90.symm)) (hcd.symm)
        · -- $b \diamond a = f$
          have hdv1 : b / a = d := div_eq_iff_mul_eq.mpr hcs1
          have hdv2 : b / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv70
          have hik : IsIdempotentElem (b / a / a) := hdv2 ▸ hidem f
          exact absurd (eq_of_mul_eq_div_div hik (hcs71.trans hdv2.symm)) (hab.symm)
      · -- $a \diamond c = f$
        exact absurd (mul_left_cancel (hcs33.trans hcs2.symm)) hce
  · -- $a \diamond d = c$
    exact absurd (mul_left_cancel (hcs1.trans hc.symm.symm)) (hbd.symm)
  · -- $a \diamond d = d$
    exact absurd (eq_of_mul_eq_self_right (hidem d) hcs1) had
  · -- $a \diamond d = e$
    rcases hspan (a * f) with hcs99 | hcs99 | hcs99 | hcs99 | hcs99 | hcs99
    · -- $a \diamond f = a$
      exact absurd (mul_left_cancel (hcs99.trans (hidem a).eq.symm)) (haf.symm)
    · -- $a \diamond f = b$
      rcases hspan (a * c) with hcs100 | hcs100 | hcs100 | hcs100 | hcs100 | hcs100
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs100.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        exact absurd (mul_left_cancel (hcs100.trans hcs99.symm)) hcf
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs100.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        have hv101 : a * e = f := by
          rcases hspan (a * e) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hae.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs99.symm)) hef
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbe.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs100.symm)) (hce.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hde.symm)
          · exact hz
        rcases hspan (b * a) with hcs102 | hcs102 | hcs102 | hcs102 | hcs102 | hcs102
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs102) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs102.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv103 : f * c = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs102))).symm.trans
              (eq677 f a)).trans hv101.symm)
          rcases hspan (c * a) with hcs104 | hcs104 | hcs104 | hcs104 | hcs104 | hcs104
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs104) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs104.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs104.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv105 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs104))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * e) with hcs106 | hcs106 | hcs106 | hcs106 | hcs106 | hcs106
            · -- $b \diamond e = a$
              have hv107 : c * b = d :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                  (eq677 a b)).trans hcs106.symm)).trans hcs1.symm)
              exact absurd (mul_left_cancel (hv107.trans hcs104.symm)) (hab.symm)
            · -- $b \diamond e = b$
              exact absurd (mul_left_cancel (hcs106.trans (hidem b).eq.symm)) (hbe.symm)
            · -- $b \diamond e = c$
              exact absurd (mul_left_cancel (hcs106.trans hcs102.symm)) (hae.symm)
            · -- $b \diamond e = d$
              rcases hspan (b * c) with hcs108 | hcs108 | hcs108 | hcs108 | hcs108 | hcs108
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs108
                have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs108.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs108.trans hcs102.symm)) (hac.symm)
              · -- $b \diamond c = d$
                exact absurd (mul_left_cancel (hcs108.trans hcs106.symm)) hce
              · -- $b \diamond c = e$
                have hv109 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs102.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs106.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs108.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv105.symm)) (hdf.symm)
                have hv110 : c * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                    (eq677 a b)).trans hv109.symm)).trans hv101.symm)
                have hv111 : b * e = f :=
                  (congrArg (b * ·) ((congrArg (f * ·) ((congrArg (· * b) hv109).trans
                    hc.symm)).trans hv103)).symm.trans (eq677 f b)
                exact absurd (hv111.symm.trans hcs106) (hdf.symm)
              · -- $b \diamond c = f$
                exact absurd (mul_left_cancel (hcs108.trans hv105.symm)) hcd
            · -- $b \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs106) hbe
            · -- $b \diamond e = f$
              exact absurd (mul_left_cancel (hcs106.trans hv105.symm)) (hde.symm)
          · -- $c \diamond a = e$
            have hv112 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs104))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * d) with hcs113 | hcs113 | hcs113 | hcs113 | hcs113 | hcs113
            · -- $b \diamond d = a$
              have hv114 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                  (eq677 a b)).trans hcs113.symm)).trans hcs100.symm)
              exact absurd (mul_left_cancel (hv114.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond d = b$
              exact absurd (mul_left_cancel (hcs113.trans (hidem b).eq.symm)) (hbd.symm)
            · -- $b \diamond d = c$
              exact absurd (mul_left_cancel (hcs113.trans hcs102.symm)) (had.symm)
            · -- $b \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs113) hbd
            · -- $b \diamond d = e$
              have e1 : b * d = a * d := hcs113.trans hcs1.symm
              have e2 : b * (a * d) = a * (a * d) := by
                rw [hcs1]
                exact hv112.trans hv101.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
            · -- $b \diamond d = f$
              exact absurd (mul_left_cancel (hcs113.trans hv112.symm)) hde
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs104.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = d$
          have hv115 : f * d = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs102))).symm.trans
              (eq677 f a)).trans hv101.symm)
          rcases hspan (c * a) with hcs116 | hcs116 | hcs116 | hcs116 | hcs116 | hcs116
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs116) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs116.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs116.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv117 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs116))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (f * b) with hcs118 | hcs118 | hcs118 | hcs118 | hcs118 | hcs118
            · -- $f \diamond b = a$
              have hdv1 : f / b = d := div_eq_iff_mul_eq.mpr hv117
              have hdv2 : f / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs102
              have hik : IsIdempotentElem (f / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs118.trans hdv2.symm)) (hbf.symm)
            · -- $f \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs118) (hbf.symm)
            · -- $f \diamond b = c$
              have hv119 : d * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                  ((congrArg (· * b) hv117).trans hcs118))).symm.trans
                  (eq677 d b)).trans hcs102.symm)
              have hdv : d / c = a := div_eq_iff_mul_eq.mpr hcs116
              have hik : IsIdempotentElem (d / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv119.trans hdv.symm)) (hcd.symm)
            · -- $f \diamond b = d$
              have hdv : f / b = d := div_eq_iff_mul_eq.mpr hv117
              have hik : IsIdempotentElem (f / b) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hcs118.trans hdv.symm)) (hbf.symm)
            · -- $f \diamond b = e$
              exact absurd (mul_left_cancel (hcs118.trans hv115.symm)) hbd
            · -- $f \diamond b = f$
              exact absurd (mul_left_cancel (hcs118.trans (hidem f).eq.symm)) hbf
          · -- $c \diamond a = e$
            have hv120 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs116))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * c) with hcs121 | hcs121 | hcs121 | hcs121 | hcs121 | hcs121
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs121
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs121.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs121) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs121.trans hcs102.symm)) (hac.symm)
            · -- $b \diamond c = e$
              rcases hspan (b * d) with hcs122 | hcs122 | hcs122 | hcs122 | hcs122 | hcs122
              · -- $b \diamond d = a$
                have hv123 : d * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                    (eq677 a b)).trans hcs122.symm)).trans hcs100.symm)
                have hv124 : d * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs122).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hcs102.symm)
                have hv125 : c * e = b :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (c * ·)
                    ((congrArg (· * d) hv124).trans hcs1))).symm.trans
                    (eq677 c d)).trans hv123.symm)
                have hdv : b / c = e := div_eq_iff_mul_eq.mpr hv125
                have hik : IsIdempotentElem (b / c) := hdv ▸ hidem e
                exact absurd (eq_of_mul_eq_div hik (hcs121.trans hdv.symm)) hbc
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs122.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv126 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs122.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs102.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs121.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv120.symm)) (hef.symm)
                have hv127 : d * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs102))).symm.trans
                    (eq677 a b)).trans hv126.symm)).trans hv101.symm)
                have hv128 : f * c = e :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv126).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hv120.symm)
                exact absurd (mul_left_cancel (hv128.trans hv115.symm)) hcd
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs122.trans hcs102.symm)) (had.symm)
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs122.trans hcs121.symm)) (hcd.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs122.trans hv120.symm)) hde
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs121.trans hv120.symm)) hce
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs116.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = e$
          have hdv1 : b / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hdv2 : b / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv101
          have hik : IsIdempotentElem (b / a / a) := hdv2 ▸ hidem e
          exact absurd (eq_of_mul_eq_div_div hik (hcs102.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hdv : b / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hik : IsIdempotentElem (b / a) := hdv ▸ hidem f
          exact absurd (eq_of_mul_eq_div hik (hcs102.trans hdv.symm)) (hab.symm)
      · -- $a \diamond c = e$
        exact absurd (mul_left_cancel (hcs100.trans hcs1.symm)) hcd
      · -- $a \diamond c = f$
        have hv129 : a * e = d := by
          rcases hspan (a * e) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hae.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs99.symm)) hef
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbe.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hde.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs100.symm)) (hce.symm)
        rcases hspan (b * a) with hcs130 | hcs130 | hcs130 | hcs130 | hcs130 | hcs130
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs130) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs130.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hdv1 : b / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hdv2 : b / a / a = c := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs100
          have hik : IsIdempotentElem (b / a / a) := hdv2 ▸ hidem c
          exact absurd (eq_of_mul_eq_div_div hik (hcs130.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = d$
          have hv131 : f * d = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs130))).symm.trans
              (eq677 f a)).trans hcs100.symm)
          rcases hspan (c * a) with hcs132 | hcs132 | hcs132 | hcs132 | hcs132 | hcs132
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs132) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs132.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs132.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv133 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs132))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (f * b) with hcs134 | hcs134 | hcs134 | hcs134 | hcs134 | hcs134
            · -- $f \diamond b = a$
              have hdv1 : f / b = d := div_eq_iff_mul_eq.mpr hv133
              have hdv2 : f / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs130
              have hik : IsIdempotentElem (f / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs134.trans hdv2.symm)) (hbf.symm)
            · -- $f \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs134) (hbf.symm)
            · -- $f \diamond b = c$
              exact absurd (mul_left_cancel (hcs134.trans hv131.symm)) hbd
            · -- $f \diamond b = d$
              have hdv : f / b = d := div_eq_iff_mul_eq.mpr hv133
              have hik : IsIdempotentElem (f / b) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hcs134.trans hdv.symm)) (hbf.symm)
            · -- $f \diamond b = e$
              have hv135 : d * e = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                  ((congrArg (· * b) hv133).trans hcs134))).symm.trans
                  (eq677 d b)).trans hcs130.symm)
              have hdv : a / d = e := div_eq_iff_mul_eq.mpr hv135
              have hik : IsIdempotentElem (a / d) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $f \diamond b = f$
              exact absurd (mul_left_cancel (hcs134.trans (hidem f).eq.symm)) hbf
          · -- $c \diamond a = e$
            have hv136 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs132))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * c) with hcs137 | hcs137 | hcs137 | hcs137 | hcs137 | hcs137
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs137
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs137.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs137) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs137.trans hcs130.symm)) (hac.symm)
            · -- $b \diamond c = e$
              rcases hspan (b * d) with hcs138 | hcs138 | hcs138 | hcs138 | hcs138 | hcs138
              · -- $b \diamond d = a$
                have hv139 : d * b = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs130))).symm.trans
                    (eq677 a b)).trans hcs138.symm)).trans hv129.symm)
                have hv140 : d * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs138).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hcs130.symm)
                have hv141 : b * f = c := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs138.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs137.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv136.symm)) (hef.symm)
                have hv142 : e * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (d * ·) (congrArg (· * a) hcs1))).symm.trans
                    (eq677 d a)).trans hv129.symm)).trans hv139.symm)
                have hv143 : e * b = a :=
                  (congrArg (e * ·) ((congrArg (a * ·) ((congrArg (· * e) hv142).trans
                    hv136)).trans hcs99)).symm.trans (eq677 a e)
                have hv144 : b * e = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs137).trans
                    hv143)).trans hcs132)).symm.trans (eq677 c b)
                exact absurd (hv144.symm.trans hv136) hcf
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs138.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv145 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs138.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs137.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv136.symm)) (hef.symm)
                have hv146 : d * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs130))).symm.trans
                    (eq677 a b)).trans hv145.symm)).trans hcs100.symm)
                have hv147 : f * c = e :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv145).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hv136.symm)
                have e1 : f * d = b * d := hv131.trans hcs138.symm
                have e2 : f * (b * d) = b * (b * d) := by
                  rw [hcs138]
                  exact hv147.trans hcs137.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbf.symm)
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs138.trans hcs130.symm)) (had.symm)
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs138.trans hcs137.symm)) (hcd.symm)
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs138.trans hv136.symm)) hde
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs137.trans hv136.symm)) hce
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs132.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = e$
          have hv148 : f * e = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs130))).symm.trans
              (eq677 f a)).trans hcs100.symm)
          rcases hspan (c * a) with hcs149 | hcs149 | hcs149 | hcs149 | hcs149 | hcs149
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs149) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs149.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs149.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv150 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs149))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (b * c) with hcs151 | hcs151 | hcs151 | hcs151 | hcs151 | hcs151
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs151
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs151.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs151) hbc
            · -- $b \diamond c = d$
              rcases hspan (b * e) with hcs152 | hcs152 | hcs152 | hcs152 | hcs152 | hcs152
              · -- $b \diamond e = a$
                have hv153 : e * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs130))).symm.trans
                    (eq677 a b)).trans hcs152.symm)).trans hcs1.symm)
                have hv154 : e * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hcs152).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hcs130.symm)
                have hv155 : b * f = c := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs152.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs151.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv150.symm)) (hdf.symm)
                have hv156 : d * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (e * ·) (congrArg (· * a) hv129))).symm.trans
                    (eq677 e a)).trans hcs1.symm)).trans hv153.symm)
                have hv157 : d * b = a :=
                  (congrArg (d * ·) ((congrArg (a * ·) ((congrArg (· * d) hv156).trans
                    hv150)).trans hcs99)).symm.trans (eq677 a d)
                have hv158 : b * d = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs151).trans
                    hv157)).trans hcs149)).symm.trans (eq677 c b)
                exact absurd (hv158.symm.trans hv150) hcf
              · -- $b \diamond e = b$
                exact absurd (mul_left_cancel (hcs152.trans (hidem b).eq.symm)) (hbe.symm)
              · -- $b \diamond e = c$
                have hv159 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs152.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs151.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs130.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv150.symm)) (hdf.symm)
                have hv160 : e * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs130))).symm.trans
                    (eq677 a b)).trans hv159.symm)).trans hcs100.symm)
                have hv161 : f * c = d :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv159).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hv150.symm)
                have e1 : f * e = b * e := hv148.trans hcs152.symm
                have e2 : f * (b * e) = b * (b * e) := by
                  rw [hcs152]
                  exact hv161.trans hcs151.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbf.symm)
              · -- $b \diamond e = d$
                exact absurd (mul_left_cancel (hcs152.trans hcs151.symm)) (hce.symm)
              · -- $b \diamond e = e$
                exact absurd (mul_left_cancel (hcs152.trans hcs130.symm)) (hae.symm)
              · -- $b \diamond e = f$
                exact absurd (mul_left_cancel (hcs152.trans hv150.symm)) (hde.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs151.trans hcs130.symm)) (hac.symm)
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs151.trans hv150.symm)) hcd
          · -- $c \diamond a = e$
            have hv162 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs149))).symm.trans
                (eq677 b a)).trans hcs99.symm)
            rcases hspan (f * b) with hcs163 | hcs163 | hcs163 | hcs163 | hcs163 | hcs163
            · -- $f \diamond b = a$
              have hdv1 : f / b = e := div_eq_iff_mul_eq.mpr hv162
              have hdv2 : f / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs130
              have hik : IsIdempotentElem (f / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs163.trans hdv2.symm)) (hbf.symm)
            · -- $f \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs163) (hbf.symm)
            · -- $f \diamond b = c$
              exact absurd (mul_left_cancel (hcs163.trans hv148.symm)) hbe
            · -- $f \diamond b = d$
              have hv164 : e * d = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                  ((congrArg (· * b) hv162).trans hcs163))).symm.trans
                  (eq677 e b)).trans hcs130.symm)
              have hdv : a / e = d := div_eq_iff_mul_eq.mpr hv164
              have hik : IsIdempotentElem (a / e) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hv129.trans hdv.symm)) hae
            · -- $f \diamond b = e$
              have hdv : f / b = e := div_eq_iff_mul_eq.mpr hv162
              have hik : IsIdempotentElem (f / b) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs163.trans hdv.symm)) (hbf.symm)
            · -- $f \diamond b = f$
              exact absurd (mul_left_cancel (hcs163.trans (hidem f).eq.symm)) hbf
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs149.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = f$
          have hdv : b / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hik : IsIdempotentElem (b / a) := hdv ▸ hidem f
          exact absurd (eq_of_mul_eq_div hik (hcs130.trans hdv.symm)) (hab.symm)
    · -- $a \diamond f = c$
      exact absurd (mul_left_cancel (hcs99.trans hc.symm.symm)) (hbf.symm)
    · -- $a \diamond f = d$
      rcases hspan (a * c) with hcs165 | hcs165 | hcs165 | hcs165 | hcs165 | hcs165
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs165.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        have hv166 : a * e = f := by
          rcases hspan (a * e) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hae.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs165.symm)) (hce.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbe.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs99.symm)) hef
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hde.symm)
          · exact hz
        rcases hspan (d * a) with hcs167 | hcs167 | hcs167 | hcs167 | hcs167 | hcs167
        · -- $d \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs167) (had.symm)
        · -- $d \diamond a = b$
          have hv168 : f * b = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs167))).symm.trans
              (eq677 f a)).trans hv166.symm)
          rcases hspan (e * a) with hcs169 | hcs169 | hcs169 | hcs169 | hcs169 | hcs169
          · -- $e \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs169) (hae.symm)
          · -- $e \diamond a = b$
            have hv170 : d * b = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
                ((congrArg (· * a) hcs1).trans hcs169))).symm.trans
                (eq677 d a)).trans hcs99.symm)
            rcases hspan (f * d) with hcs171 | hcs171 | hcs171 | hcs171 | hcs171 | hcs171
            · -- $f \diamond d = a$
              have hdv1 : f / d = b := div_eq_iff_mul_eq.mpr hv170
              have hdv2 : f / d / d = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs167
              have hik : IsIdempotentElem (f / d / d) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs171.trans hdv2.symm)) (hdf.symm)
            · -- $f \diamond d = b$
              have hdv : f / d = b := div_eq_iff_mul_eq.mpr hv170
              have hik : IsIdempotentElem (f / d) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs171.trans hdv.symm)) (hdf.symm)
            · -- $f \diamond d = c$
              have hv172 : b * c = a :=
                mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                  ((congrArg (· * d) hv170).trans hcs171))).symm.trans
                  (eq677 b d)).trans hcs167.symm)
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hv172
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $f \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs171) (hdf.symm)
            · -- $f \diamond d = e$
              exact absurd (mul_left_cancel (hcs171.trans hv168.symm)) (hbd.symm)
            · -- $f \diamond d = f$
              exact absurd (mul_left_cancel (hcs171.trans (hidem f).eq.symm)) hdf
          · -- $e \diamond a = c$
            have hv173 : d * c = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
                ((congrArg (· * a) hcs1).trans hcs169))).symm.trans
                (eq677 d a)).trans hcs99.symm)
            rcases hspan (d * e) with hcs174 | hcs174 | hcs174 | hcs174 | hcs174 | hcs174
            · -- $d \diamond e = a$
              have hdv : a / d = e := div_eq_iff_mul_eq.mpr hcs174
              have hik : IsIdempotentElem (a / d) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $d \diamond e = b$
              exact absurd (mul_left_cancel (hcs174.trans hcs167.symm)) (hae.symm)
            · -- $d \diamond e = c$
              rcases hspan (d * b) with hcs175 | hcs175 | hcs175 | hcs175 | hcs175 | hcs175
              · -- $d \diamond b = a$
                have hv176 : b * d = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                    (congrArg (a * ·) (congrArg (· * d) hcs167))).symm.trans
                    (eq677 a d)).trans hcs175.symm)).trans hcs165.symm)
                have hv177 : b * e = a :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (b * ·)
                    ((congrArg (· * d) hcs175).trans hcs1))).symm.trans
                    (eq677 b d)).trans hcs167.symm)
                have hv178 : d * f = e := by
                  rcases hspan (d * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs175.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs167.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs174.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem d).eq.symm)) (hdf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hv173.symm)) (hcf.symm)
                have hv179 : c * a = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (b * ·) (congrArg (· * a) hc.symm))).symm.trans
                    (eq677 b a)).trans hcs165.symm)).trans hv176.symm)
                have hv180 : c * d = a :=
                  (congrArg (c * ·) ((congrArg (a * ·) ((congrArg (· * c) hv179).trans
                    hv173)).trans hcs99)).symm.trans (eq677 a c)
                have hv181 : d * c = e :=
                  (congrArg (d * ·) ((congrArg (e * ·) ((congrArg (· * d) hcs174).trans
                    hv180)).trans hcs169)).symm.trans (eq677 e d)
                exact absurd (hv181.symm.trans hv173) hef
              · -- $d \diamond b = b$
                exact absurd (mul_left_cancel (hcs175.trans hcs167.symm)) (hab.symm)
              · -- $d \diamond b = c$
                exact absurd (mul_left_cancel (hcs175.trans hcs174.symm)) hbe
              · -- $d \diamond b = d$
                exact absurd (mul_left_cancel (hcs175.trans (hidem d).eq.symm)) hbd
              · -- $d \diamond b = e$
                have hv182 : d * f = a := by
                  rcases hspan (d * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs167.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs174.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem d).eq.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs175.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv173.symm)) (hcf.symm)
                have hv183 : b * d = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                    (congrArg (a * ·) (congrArg (· * d) hcs167))).symm.trans
                    (eq677 a d)).trans hv182.symm)).trans hv166.symm)
                have hv184 : f * e = c :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (f * ·)
                    ((congrArg (· * d) hv182).trans hcs1))).symm.trans
                    (eq677 f d)).trans hv173.symm)
                have e1 : f * b = d * b := hv168.trans hcs175.symm
                have e2 : f * (d * b) = d * (d * b) := by
                  rw [hcs175]
                  exact hv184.trans hcs174.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hdf.symm)
              · -- $d \diamond b = f$
                exact absurd (mul_left_cancel (hcs175.trans hv173.symm)) hbc
            · -- $d \diamond e = d$
              exact absurd (mul_left_cancel (hcs174.trans (hidem d).eq.symm)) (hde.symm)
            · -- $d \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs174) hde
            · -- $d \diamond e = f$
              exact absurd (mul_left_cancel (hcs174.trans hv173.symm)) (hce.symm)
          · -- $e \diamond a = d$
            have hdv : e / a = d := div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (e / a) := hdv ▸ hidem d
            exact absurd (eq_of_mul_eq_div hik (hcs169.trans hdv.symm)) (hae.symm)
          · -- $e \diamond a = e$
            exact absurd (mul_left_cancel (hcs169.trans (hidem e).eq.symm)) hae
          · -- $e \diamond a = f$
            have hdv1 : e / a = d := div_eq_iff_mul_eq.mpr hcs1
            have hdv2 : e / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : IsIdempotentElem (e / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs169.trans hdv2.symm)) (hae.symm)
        · -- $d \diamond a = c$
          have hv185 : f * c = e :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hcs99).trans hcs167))).symm.trans
              (eq677 f a)).trans hv166.symm)
          rcases hspan (e * a) with hcs186 | hcs186 | hcs186 | hcs186 | hcs186 | hcs186
          · -- $e \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs186) (hae.symm)
          · -- $e \diamond a = b$
            have hv187 : d * b = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
                ((congrArg (· * a) hcs1).trans hcs186))).symm.trans
                (eq677 d a)).trans hcs99.symm)
            rcases hspan (d * e) with hcs188 | hcs188 | hcs188 | hcs188 | hcs188 | hcs188
            · -- $d \diamond e = a$
              have hdv : a / d = e := div_eq_iff_mul_eq.mpr hcs188
              have hik : IsIdempotentElem (a / d) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $d \diamond e = b$
              rcases hspan (d * c) with hcs189 | hcs189 | hcs189 | hcs189 | hcs189 | hcs189
              · -- $d \diamond c = a$
                have hv190 : c * d = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                    (congrArg (a * ·) (congrArg (· * d) hcs167))).symm.trans
                    (eq677 a d)).trans hcs189.symm)).trans hc.symm.symm)
                have hv191 : c * e = a :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (c * ·)
                    ((congrArg (· * d) hcs189).trans hcs1))).symm.trans
                    (eq677 c d)).trans hcs167.symm)
                have hv192 : d * f = e := by
                  rcases hspan (d * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs189.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs188.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs167.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem d).eq.symm)) (hdf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hv187.symm)) (hbf.symm)
                have hv193 : b * a = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (c * ·) (congrArg (· * a) hcs165))).symm.trans
                    (eq677 c a)).trans hc.symm.symm)).trans hv190.symm)
                have hv194 : b * d = a :=
                  (congrArg (b * ·) ((congrArg (a * ·) ((congrArg (· * b) hv193).trans
                    hv187)).trans hcs99)).symm.trans (eq677 a b)
                have hv195 : d * b = e :=
                  (congrArg (d * ·) ((congrArg (e * ·) ((congrArg (· * d) hcs188).trans
                    hv194)).trans hcs186)).symm.trans (eq677 e d)
                exact absurd (hv195.symm.trans hv187) hef
              · -- $d \diamond c = b$
                exact absurd (mul_left_cancel (hcs189.trans hcs188.symm)) hce
              · -- $d \diamond c = c$
                exact absurd (mul_left_cancel (hcs189.trans hcs167.symm)) (hac.symm)
              · -- $d \diamond c = d$
                exact absurd (mul_left_cancel (hcs189.trans (hidem d).eq.symm)) hcd
              · -- $d \diamond c = e$
                have hv196 : d * f = a := by
                  rcases hspan (d * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs188.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs167.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem d).eq.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs189.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv187.symm)) (hbf.symm)
                have hv197 : c * d = e :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (d * ·)
                    (congrArg (a * ·) (congrArg (· * d) hcs167))).symm.trans
                    (eq677 a d)).trans hv196.symm)).trans hv166.symm)
                have hv198 : f * e = b :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (f * ·)
                    ((congrArg (· * d) hv196).trans hcs1))).symm.trans
                    (eq677 f d)).trans hv187.symm)
                have e1 : f * c = d * c := hv185.trans hcs189.symm
                have e2 : f * (d * c) = d * (d * c) := by
                  rw [hcs189]
                  exact hv198.trans hcs188.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hdf.symm)
              · -- $d \diamond c = f$
                exact absurd (mul_left_cancel (hcs189.trans hv187.symm)) (hbc.symm)
            · -- $d \diamond e = c$
              exact absurd (mul_left_cancel (hcs188.trans hcs167.symm)) (hae.symm)
            · -- $d \diamond e = d$
              exact absurd (mul_left_cancel (hcs188.trans (hidem d).eq.symm)) (hde.symm)
            · -- $d \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs188) hde
            · -- $d \diamond e = f$
              exact absurd (mul_left_cancel (hcs188.trans hv187.symm)) (hbe.symm)
          · -- $e \diamond a = c$
            have hv199 : d * c = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (d * ·)
                ((congrArg (· * a) hcs1).trans hcs186))).symm.trans
                (eq677 d a)).trans hcs99.symm)
            rcases hspan (f * d) with hcs200 | hcs200 | hcs200 | hcs200 | hcs200 | hcs200
            · -- $f \diamond d = a$
              have hdv1 : f / d = c := div_eq_iff_mul_eq.mpr hv199
              have hdv2 : f / d / d = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs167
              have hik : IsIdempotentElem (f / d / d) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs200.trans hdv2.symm)) (hdf.symm)
            · -- $f \diamond d = b$
              have hv201 : c * b = a :=
                mul_left_cancel (((congrArg (d * ·) (congrArg (c * ·)
                  ((congrArg (· * d) hv199).trans hcs200))).symm.trans
                  (eq677 c d)).trans hcs167.symm)
              have hdv : a / c = b := div_eq_iff_mul_eq.mpr hv201
              have hik : IsIdempotentElem (a / c) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs165.trans hdv.symm)) hac
            · -- $f \diamond d = c$
              have hdv : f / d = c := div_eq_iff_mul_eq.mpr hv199
              have hik : IsIdempotentElem (f / d) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hcs200.trans hdv.symm)) (hdf.symm)
            · -- $f \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs200) (hdf.symm)
            · -- $f \diamond d = e$
              exact absurd (mul_left_cancel (hcs200.trans hv185.symm)) (hcd.symm)
            · -- $f \diamond d = f$
              exact absurd (mul_left_cancel (hcs200.trans (hidem f).eq.symm)) hdf
          · -- $e \diamond a = d$
            have hdv : e / a = d := div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (e / a) := hdv ▸ hidem d
            exact absurd (eq_of_mul_eq_div hik (hcs186.trans hdv.symm)) (hae.symm)
          · -- $e \diamond a = e$
            exact absurd (mul_left_cancel (hcs186.trans (hidem e).eq.symm)) hae
          · -- $e \diamond a = f$
            have hdv1 : e / a = d := div_eq_iff_mul_eq.mpr hcs1
            have hdv2 : e / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs99
            have hik : IsIdempotentElem (e / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs186.trans hdv2.symm)) (hae.symm)
        · -- $d \diamond a = d$
          exact absurd (mul_left_cancel (hcs167.trans (hidem d).eq.symm)) had
        · -- $d \diamond a = e$
          have hdv1 : d / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hdv2 : d / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv166
          have hik : IsIdempotentElem (d / a / a) := hdv2 ▸ hidem e
          exact absurd (eq_of_mul_eq_div_div hik (hcs167.trans hdv2.symm)) (had.symm)
        · -- $d \diamond a = f$
          have hdv : d / a = f := div_eq_iff_mul_eq.mpr hcs99
          have hik : IsIdempotentElem (d / a) := hdv ▸ hidem f
          exact absurd (eq_of_mul_eq_div hik (hcs167.trans hdv.symm)) (had.symm)
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs165.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        exact absurd (mul_left_cancel (hcs165.trans hcs99.symm)) hcf
      · -- $a \diamond c = e$
        exact absurd (mul_left_cancel (hcs165.trans hcs1.symm)) hcd
      · -- $a \diamond c = f$
        have hv202 : a * e = b := by
          rcases hspan (a * e) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (hae.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbe.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs99.symm)) hef
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hde.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs165.symm)) (hce.symm)
        rcases hspan (b * a) with hcs203 | hcs203 | hcs203 | hcs203 | hcs203 | hcs203
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs203) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs203.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv204 : e * c = d :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hv202).trans hcs203))).symm.trans
              (eq677 e a)).trans hcs1.symm)
          rcases hspan (c * a) with hcs205 | hcs205 | hcs205 | hcs205 | hcs205 | hcs205
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs205) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs205.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs205.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv206 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs205))).symm.trans
                (eq677 b a)).trans hv202.symm)
            rcases hspan (b * f) with hcs207 | hcs207 | hcs207 | hcs207 | hcs207 | hcs207
            · -- $b \diamond f = a$
              have hv208 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                  (eq677 a b)).trans hcs207.symm)).trans hcs165.symm)
              exact absurd (mul_left_cancel (hv208.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond f = b$
              exact absurd (mul_left_cancel (hcs207.trans (hidem b).eq.symm)) (hbf.symm)
            · -- $b \diamond f = c$
              exact absurd (mul_left_cancel (hcs207.trans hcs203.symm)) (haf.symm)
            · -- $b \diamond f = d$
              have e1 : b * f = a * f := hcs207.trans hcs99.symm
              have e2 : b * (a * f) = a * (a * f) := by
                rw [hcs99]
                exact hv206.trans hcs1.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
            · -- $b \diamond f = e$
              exact absurd (mul_left_cancel (hcs207.trans hv206.symm)) (hdf.symm)
            · -- $b \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs207) hbf
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv202
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs205.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv209 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs205))).symm.trans
                (eq677 b a)).trans hv202.symm)
            rcases hspan (b * d) with hcs210 | hcs210 | hcs210 | hcs210 | hcs210 | hcs210
            · -- $b \diamond d = a$
              have hv211 : c * b = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                  (eq677 a b)).trans hcs210.symm)).trans hcs99.symm)
              exact absurd (mul_left_cancel (hv211.trans hcs205.symm)) (hab.symm)
            · -- $b \diamond d = b$
              exact absurd (mul_left_cancel (hcs210.trans (hidem b).eq.symm)) (hbd.symm)
            · -- $b \diamond d = c$
              exact absurd (mul_left_cancel (hcs210.trans hcs203.symm)) (had.symm)
            · -- $b \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs210) hbd
            · -- $b \diamond d = e$
              exact absurd (mul_left_cancel (hcs210.trans hv209.symm)) hdf
            · -- $b \diamond d = f$
              rcases hspan (b * c) with hcs212 | hcs212 | hcs212 | hcs212 | hcs212 | hcs212
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs212
                have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs212.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs212.trans hcs203.symm)) (hac.symm)
              · -- $b \diamond c = d$
                have hv213 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs203.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs212.symm)) (hce.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv209.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs210.symm)) (hde.symm)
                have hv214 : c * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                    (eq677 a b)).trans hv213.symm)).trans hcs1.symm)
                have hv215 : b * d = e :=
                  (congrArg (b * ·) ((congrArg (e * ·) ((congrArg (· * b) hv213).trans
                    hc.symm)).trans hv204)).symm.trans (eq677 e b)
                exact absurd (hv215.symm.trans hcs210) hef
              · -- $b \diamond c = e$
                exact absurd (mul_left_cancel (hcs212.trans hv209.symm)) hcf
              · -- $b \diamond c = f$
                exact absurd (mul_left_cancel (hcs212.trans hcs210.symm)) hcd
        · -- $b \diamond a = d$
          have hdv1 : b / a = e := div_eq_iff_mul_eq.mpr hv202
          have hdv2 : b / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
          have hik : IsIdempotentElem (b / a / a) := hdv2 ▸ hidem d
          exact absurd (eq_of_mul_eq_div_div hik (hcs203.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hdv : b / a = e := div_eq_iff_mul_eq.mpr hv202
          have hik : IsIdempotentElem (b / a) := hdv ▸ hidem e
          exact absurd (eq_of_mul_eq_div hik (hcs203.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hv216 : e * f = d :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hv202).trans hcs203))).symm.trans
              (eq677 e a)).trans hcs1.symm)
          rcases hspan (c * a) with hcs217 | hcs217 | hcs217 | hcs217 | hcs217 | hcs217
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs217) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs217.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs217.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv218 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs217))).symm.trans
                (eq677 b a)).trans hv202.symm)
            rcases hspan (b * c) with hcs219 | hcs219 | hcs219 | hcs219 | hcs219 | hcs219
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs219
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs219.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs219) hbc
            · -- $b \diamond c = d$
              rcases hspan (b * e) with hcs220 | hcs220 | hcs220 | hcs220 | hcs220 | hcs220
              · -- $b \diamond e = a$
                have hv221 : f * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                    (eq677 a b)).trans hcs220.symm)).trans hcs1.symm)
                have hv222 : e * c = d :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hcs220).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hv218.symm)
                exact absurd (mul_left_cancel (hv222.trans hv216.symm)) hcf
              · -- $b \diamond e = b$
                exact absurd (mul_left_cancel (hcs220.trans (hidem b).eq.symm)) (hbe.symm)
              · -- $b \diamond e = c$
                have hv223 : c * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (e * ·) (congrArg (· * b) hcs220))).symm.trans
                    (eq677 e b)).trans hv218.symm)).trans hv216.symm)
                have hv224 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs220.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs219.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv218.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs203.symm)) (haf.symm)
                have hv225 : f * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs203))).symm.trans
                    (eq677 a b)).trans hv224.symm)).trans hcs165.symm)
                have hv226 : f * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv224).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hcs203.symm)
                have hv227 : c * f = b :=
                  (congrArg (c * ·) ((congrArg (b * ·) ((congrArg (· * c) hv223).trans
                    hv226)).trans hcs203)).symm.trans (eq677 b c)
                have hdv : c / f = b := div_eq_iff_mul_eq.mpr hv225
                have hik : IsIdempotentElem (c / f) := hdv ▸ hidem b
                exact absurd (eq_of_mul_eq_div hik (hv227.trans hdv.symm)) hcf
              · -- $b \diamond e = d$
                exact absurd (mul_left_cancel (hcs220.trans hcs219.symm)) (hce.symm)
              · -- $b \diamond e = e$
                exact absurd (mul_left_cancel (hcs220.trans hv218.symm)) (hde.symm)
              · -- $b \diamond e = f$
                exact absurd (mul_left_cancel (hcs220.trans hcs203.symm)) (hae.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs219.trans hv218.symm)) hcd
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs219.trans hcs203.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv202
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs217.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv228 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs217))).symm.trans
                (eq677 b a)).trans hv202.symm)
            rcases hspan (e * b) with hcs229 | hcs229 | hcs229 | hcs229 | hcs229 | hcs229
            · -- $e \diamond b = a$
              have hdv1 : e / b = f := div_eq_iff_mul_eq.mpr hv228
              have hdv2 : e / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs203
              have hik : IsIdempotentElem (e / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs229.trans hdv2.symm)) (hbe.symm)
            · -- $e \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs229) (hbe.symm)
            · -- $e \diamond b = c$
              have hv230 : f * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                  ((congrArg (· * b) hv228).trans hcs229))).symm.trans
                  (eq677 f b)).trans hcs203.symm)
              have hdv : f / c = a := div_eq_iff_mul_eq.mpr hcs217
              have hik : IsIdempotentElem (f / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv230.trans hdv.symm)) (hcf.symm)
            · -- $e \diamond b = d$
              exact absurd (mul_left_cancel (hcs229.trans hv216.symm)) hbf
            · -- $e \diamond b = e$
              exact absurd (mul_left_cancel (hcs229.trans (hidem e).eq.symm)) hbe
            · -- $e \diamond b = f$
              have hdv : e / b = f := div_eq_iff_mul_eq.mpr hv228
              have hik : IsIdempotentElem (e / b) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs229.trans hdv.symm)) (hbe.symm)
    · -- $a \diamond f = e$
      exact absurd (mul_left_cancel (hcs99.trans hcs1.symm)) (hdf.symm)
    · -- $a \diamond f = f$
      exact absurd (eq_of_mul_eq_self_right (hidem f) hcs99) haf
  · -- $a \diamond d = f$
    rcases hspan (a * e) with hcs231 | hcs231 | hcs231 | hcs231 | hcs231 | hcs231
    · -- $a \diamond e = a$
      exact absurd (mul_left_cancel (hcs231.trans (hidem a).eq.symm)) (hae.symm)
    · -- $a \diamond e = b$
      rcases hspan (a * c) with hcs232 | hcs232 | hcs232 | hcs232 | hcs232 | hcs232
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs232.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        exact absurd (mul_left_cancel (hcs232.trans hcs231.symm)) hce
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs232.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        have hv233 : a * f = e := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs231.symm)) (hef.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs232.symm)) (hcf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
        rcases hspan (b * a) with hcs234 | hcs234 | hcs234 | hcs234 | hcs234 | hcs234
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs234) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs234.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv235 : e * c = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs234))).symm.trans
              (eq677 e a)).trans hv233.symm)
          rcases hspan (c * a) with hcs236 | hcs236 | hcs236 | hcs236 | hcs236 | hcs236
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs236) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs236.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs236.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv237 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs236))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * f) with hcs238 | hcs238 | hcs238 | hcs238 | hcs238 | hcs238
            · -- $b \diamond f = a$
              have hv239 : c * b = d :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                  (eq677 a b)).trans hcs238.symm)).trans hcs1.symm)
              exact absurd (mul_left_cancel (hv239.trans hcs236.symm)) (hab.symm)
            · -- $b \diamond f = b$
              exact absurd (mul_left_cancel (hcs238.trans (hidem b).eq.symm)) (hbf.symm)
            · -- $b \diamond f = c$
              exact absurd (mul_left_cancel (hcs238.trans hcs234.symm)) (haf.symm)
            · -- $b \diamond f = d$
              rcases hspan (b * c) with hcs240 | hcs240 | hcs240 | hcs240 | hcs240 | hcs240
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs240
                have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs240.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs240.trans hcs234.symm)) (hac.symm)
              · -- $b \diamond c = d$
                exact absurd (mul_left_cancel (hcs240.trans hcs238.symm)) hcf
              · -- $b \diamond c = e$
                exact absurd (mul_left_cancel (hcs240.trans hv237.symm)) hcd
              · -- $b \diamond c = f$
                have hv241 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs234.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs238.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hv237.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs240.symm)) (hce.symm)
                have hv242 : c * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                    (eq677 a b)).trans hv241.symm)).trans hv233.symm)
                have hv243 : b * f = e :=
                  (congrArg (b * ·) ((congrArg (e * ·) ((congrArg (· * b) hv241).trans
                    hc.symm)).trans hv235)).symm.trans (eq677 e b)
                exact absurd (hv243.symm.trans hcs238) (hde.symm)
            · -- $b \diamond f = e$
              exact absurd (mul_left_cancel (hcs238.trans hv237.symm)) (hdf.symm)
            · -- $b \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs238) hbf
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs231
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs236.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv244 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs236))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * d) with hcs245 | hcs245 | hcs245 | hcs245 | hcs245 | hcs245
            · -- $b \diamond d = a$
              have hv246 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                  (eq677 a b)).trans hcs245.symm)).trans hcs232.symm)
              exact absurd (mul_left_cancel (hv246.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond d = b$
              exact absurd (mul_left_cancel (hcs245.trans (hidem b).eq.symm)) (hbd.symm)
            · -- $b \diamond d = c$
              exact absurd (mul_left_cancel (hcs245.trans hcs234.symm)) (had.symm)
            · -- $b \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs245) hbd
            · -- $b \diamond d = e$
              exact absurd (mul_left_cancel (hcs245.trans hv244.symm)) hdf
            · -- $b \diamond d = f$
              have e1 : b * d = a * d := hcs245.trans hcs1.symm
              have e2 : b * (a * d) = a * (a * d) := by
                rw [hcs1]
                exact hv244.trans hv233.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
        · -- $b \diamond a = d$
          have hv247 : e * d = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs234))).symm.trans
              (eq677 e a)).trans hv233.symm)
          rcases hspan (c * a) with hcs248 | hcs248 | hcs248 | hcs248 | hcs248 | hcs248
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs248) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs248.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs248.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv249 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs248))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (e * b) with hcs250 | hcs250 | hcs250 | hcs250 | hcs250 | hcs250
            · -- $e \diamond b = a$
              have hdv1 : e / b = d := div_eq_iff_mul_eq.mpr hv249
              have hdv2 : e / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs234
              have hik : IsIdempotentElem (e / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs250.trans hdv2.symm)) (hbe.symm)
            · -- $e \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs250) (hbe.symm)
            · -- $e \diamond b = c$
              have hv251 : d * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                  ((congrArg (· * b) hv249).trans hcs250))).symm.trans
                  (eq677 d b)).trans hcs234.symm)
              have hdv : d / c = a := div_eq_iff_mul_eq.mpr hcs248
              have hik : IsIdempotentElem (d / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv251.trans hdv.symm)) (hcd.symm)
            · -- $e \diamond b = d$
              have hdv : e / b = d := div_eq_iff_mul_eq.mpr hv249
              have hik : IsIdempotentElem (e / b) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hcs250.trans hdv.symm)) (hbe.symm)
            · -- $e \diamond b = e$
              exact absurd (mul_left_cancel (hcs250.trans (hidem e).eq.symm)) hbe
            · -- $e \diamond b = f$
              exact absurd (mul_left_cancel (hcs250.trans hv247.symm)) hbd
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs231
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs248.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv252 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs248))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * c) with hcs253 | hcs253 | hcs253 | hcs253 | hcs253 | hcs253
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs253
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs253.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs253) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs253.trans hcs234.symm)) (hac.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs253.trans hv252.symm)) hcf
            · -- $b \diamond c = f$
              rcases hspan (b * d) with hcs254 | hcs254 | hcs254 | hcs254 | hcs254 | hcs254
              · -- $b \diamond d = a$
                have hv255 : d * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                    (eq677 a b)).trans hcs254.symm)).trans hcs232.symm)
                have hv256 : d * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs254).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hcs234.symm)
                have hv257 : c * f = b :=
                  mul_left_cancel (((congrArg (d * ·) (congrArg (c * ·)
                    ((congrArg (· * d) hv256).trans hcs1))).symm.trans
                    (eq677 c d)).trans hv255.symm)
                have hdv : b / c = f := div_eq_iff_mul_eq.mpr hv257
                have hik : IsIdempotentElem (b / c) := hdv ▸ hidem f
                exact absurd (eq_of_mul_eq_div hik (hcs253.trans hdv.symm)) hbc
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs254.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv258 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs254.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs234.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv252.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs253.symm)) (hce.symm)
                have hv259 : d * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs234))).symm.trans
                    (eq677 a b)).trans hv258.symm)).trans hv233.symm)
                have hv260 : e * c = f :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hv258).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hv252.symm)
                exact absurd (mul_left_cancel (hv260.trans hv247.symm)) hcd
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs254.trans hcs234.symm)) (had.symm)
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs254.trans hv252.symm)) hdf
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs254.trans hcs253.symm)) (hcd.symm)
        · -- $b \diamond a = e$
          have hdv : b / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hik : IsIdempotentElem (b / a) := hdv ▸ hidem e
          exact absurd (eq_of_mul_eq_div hik (hcs234.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hdv1 : b / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hdv2 : b / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv233
          have hik : IsIdempotentElem (b / a / a) := hdv2 ▸ hidem f
          exact absurd (eq_of_mul_eq_div_div hik (hcs234.trans hdv2.symm)) (hab.symm)
      · -- $a \diamond c = e$
        have hv261 : a * f = d := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs231.symm)) (hef.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs232.symm)) (hcf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
        rcases hspan (b * a) with hcs262 | hcs262 | hcs262 | hcs262 | hcs262 | hcs262
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs262) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs262.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hdv1 : b / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hdv2 : b / a / a = c := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs232
          have hik : IsIdempotentElem (b / a / a) := hdv2 ▸ hidem c
          exact absurd (eq_of_mul_eq_div_div hik (hcs262.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = d$
          have hv263 : e * d = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs262))).symm.trans
              (eq677 e a)).trans hcs232.symm)
          rcases hspan (c * a) with hcs264 | hcs264 | hcs264 | hcs264 | hcs264 | hcs264
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs264) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs264.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs264.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv265 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs264))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (e * b) with hcs266 | hcs266 | hcs266 | hcs266 | hcs266 | hcs266
            · -- $e \diamond b = a$
              have hdv1 : e / b = d := div_eq_iff_mul_eq.mpr hv265
              have hdv2 : e / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs262
              have hik : IsIdempotentElem (e / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs266.trans hdv2.symm)) (hbe.symm)
            · -- $e \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs266) (hbe.symm)
            · -- $e \diamond b = c$
              exact absurd (mul_left_cancel (hcs266.trans hv263.symm)) hbd
            · -- $e \diamond b = d$
              have hdv : e / b = d := div_eq_iff_mul_eq.mpr hv265
              have hik : IsIdempotentElem (e / b) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hcs266.trans hdv.symm)) (hbe.symm)
            · -- $e \diamond b = e$
              exact absurd (mul_left_cancel (hcs266.trans (hidem e).eq.symm)) hbe
            · -- $e \diamond b = f$
              have hv267 : d * f = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                  ((congrArg (· * b) hv265).trans hcs266))).symm.trans
                  (eq677 d b)).trans hcs262.symm)
              have hdv : a / d = f := div_eq_iff_mul_eq.mpr hv267
              have hik : IsIdempotentElem (a / d) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs231
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs264.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv268 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs264))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * c) with hcs269 | hcs269 | hcs269 | hcs269 | hcs269 | hcs269
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs269
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs269.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs269) hbc
            · -- $b \diamond c = d$
              exact absurd (mul_left_cancel (hcs269.trans hcs262.symm)) (hac.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs269.trans hv268.symm)) hcf
            · -- $b \diamond c = f$
              rcases hspan (b * d) with hcs270 | hcs270 | hcs270 | hcs270 | hcs270 | hcs270
              · -- $b \diamond d = a$
                have hv271 : d * b = f :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs262))).symm.trans
                    (eq677 a b)).trans hcs270.symm)).trans hv261.symm)
                have hv272 : d * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (d * ·)
                    ((congrArg (· * b) hcs270).trans hc.symm))).symm.trans
                    (eq677 d b)).trans hcs262.symm)
                have hv273 : b * e = c := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs270.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs262.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv268.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs269.symm)) (hce.symm)
                have hv274 : f * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (d * ·) (congrArg (· * a) hcs1))).symm.trans
                    (eq677 d a)).trans hv261.symm)).trans hv271.symm)
                have hv275 : f * b = a :=
                  (congrArg (f * ·) ((congrArg (a * ·) ((congrArg (· * f) hv274).trans
                    hv268)).trans hcs231)).symm.trans (eq677 a f)
                have hv276 : b * f = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs269).trans
                    hv275)).trans hcs264)).symm.trans (eq677 c b)
                exact absurd (hv276.symm.trans hv268) hce
              · -- $b \diamond d = b$
                exact absurd (mul_left_cancel (hcs270.trans (hidem b).eq.symm)) (hbd.symm)
              · -- $b \diamond d = c$
                have hv277 : b * e = a := by
                  rcases hspan (b * e) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbe.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs270.symm)) (hde.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs262.symm)) (hae.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv268.symm)) hef
                  · exact absurd (mul_left_cancel (hz.trans hcs269.symm)) (hce.symm)
                have hv278 : d * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs262))).symm.trans
                    (eq677 a b)).trans hv277.symm)).trans hcs232.symm)
                have hv279 : e * c = f :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hv277).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hv268.symm)
                have e1 : e * d = b * d := hv263.trans hcs270.symm
                have e2 : e * (b * d) = b * (b * d) := by
                  rw [hcs270]
                  exact hv279.trans hcs269.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbe.symm)
              · -- $b \diamond d = d$
                exact absurd (mul_left_cancel (hcs270.trans hcs262.symm)) (had.symm)
              · -- $b \diamond d = e$
                exact absurd (mul_left_cancel (hcs270.trans hv268.symm)) hdf
              · -- $b \diamond d = f$
                exact absurd (mul_left_cancel (hcs270.trans hcs269.symm)) (hcd.symm)
        · -- $b \diamond a = e$
          have hdv : b / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hik : IsIdempotentElem (b / a) := hdv ▸ hidem e
          exact absurd (eq_of_mul_eq_div hik (hcs262.trans hdv.symm)) (hab.symm)
        · -- $b \diamond a = f$
          have hv280 : e * f = c :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs262))).symm.trans
              (eq677 e a)).trans hcs232.symm)
          rcases hspan (c * a) with hcs281 | hcs281 | hcs281 | hcs281 | hcs281 | hcs281
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs281) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs281.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs281.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv282 : b * d = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs281))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (b * c) with hcs283 | hcs283 | hcs283 | hcs283 | hcs283 | hcs283
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs283
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs283.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs283) hbc
            · -- $b \diamond c = d$
              rcases hspan (b * e) with hcs284 | hcs284 | hcs284 | hcs284 | hcs284 | hcs284
              · -- $b \diamond e = a$
                have hv285 : f * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs262))).symm.trans
                    (eq677 a b)).trans hcs284.symm)).trans hcs232.symm)
                have hv286 : e * c = d :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hcs284).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hv282.symm)
                have hv287 : b * f = c := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact absurd (mul_left_cancel (hz.trans hcs284.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans hcs283.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv282.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs262.symm)) (haf.symm)
                have e1 : e * f = b * f := hv280.trans hv287.symm
                have e2 : e * (b * f) = b * (b * f) := by
                  rw [hv287]
                  exact hv286.trans hcs283.symm
                exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hbe.symm)
              · -- $b \diamond e = b$
                exact absurd (mul_left_cancel (hcs284.trans (hidem b).eq.symm)) (hbe.symm)
              · -- $b \diamond e = c$
                have hv288 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs284.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs283.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv282.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs262.symm)) (haf.symm)
                have hv289 : f * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs262))).symm.trans
                    (eq677 a b)).trans hv288.symm)).trans hcs1.symm)
                have hv290 : f * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv288).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hcs262.symm)
                have hv291 : d * a = b :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                    (congrArg (f * ·) (congrArg (· * a) hv261))).symm.trans
                    (eq677 f a)).trans hcs1.symm)).trans hv289.symm)
                have hv292 : d * b = a :=
                  (congrArg (d * ·) ((congrArg (a * ·) ((congrArg (· * d) hv291).trans
                    hv282)).trans hcs231)).symm.trans (eq677 a d)
                have hv293 : b * d = c :=
                  (congrArg (b * ·) ((congrArg (c * ·) ((congrArg (· * b) hcs283).trans
                    hv292)).trans hcs281)).symm.trans (eq677 c b)
                exact absurd (hv293.symm.trans hv282) hce
              · -- $b \diamond e = d$
                exact absurd (mul_left_cancel (hcs284.trans hcs283.symm)) (hce.symm)
              · -- $b \diamond e = e$
                exact absurd (mul_left_cancel (hcs284.trans hv282.symm)) (hde.symm)
              · -- $b \diamond e = f$
                exact absurd (mul_left_cancel (hcs284.trans hcs262.symm)) (hae.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs283.trans hv282.symm)) hcd
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs283.trans hcs262.symm)) (hac.symm)
          · -- $c \diamond a = e$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = e := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs231
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem e
            exact absurd (eq_of_mul_eq_div_div hik (hcs281.trans hdv2.symm)) (hac.symm)
          · -- $c \diamond a = f$
            have hv294 : b * f = e :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs281))).symm.trans
                (eq677 b a)).trans hcs231.symm)
            rcases hspan (e * b) with hcs295 | hcs295 | hcs295 | hcs295 | hcs295 | hcs295
            · -- $e \diamond b = a$
              have hdv1 : e / b = f := div_eq_iff_mul_eq.mpr hv294
              have hdv2 : e / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs262
              have hik : IsIdempotentElem (e / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs295.trans hdv2.symm)) (hbe.symm)
            · -- $e \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs295) (hbe.symm)
            · -- $e \diamond b = c$
              exact absurd (mul_left_cancel (hcs295.trans hv280.symm)) hbf
            · -- $e \diamond b = d$
              have hv296 : f * d = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                  ((congrArg (· * b) hv294).trans hcs295))).symm.trans
                  (eq677 f b)).trans hcs262.symm)
              have hdv : a / f = d := div_eq_iff_mul_eq.mpr hv296
              have hik : IsIdempotentElem (a / f) := hdv ▸ hidem d
              exact absurd (eq_of_mul_eq_div hik (hv261.trans hdv.symm)) haf
            · -- $e \diamond b = e$
              exact absurd (mul_left_cancel (hcs295.trans (hidem e).eq.symm)) hbe
            · -- $e \diamond b = f$
              have hdv : e / b = f := div_eq_iff_mul_eq.mpr hv294
              have hik : IsIdempotentElem (e / b) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs295.trans hdv.symm)) (hbe.symm)
      · -- $a \diamond c = f$
        exact absurd (mul_left_cancel (hcs232.trans hcs1.symm)) hcd
    · -- $a \diamond e = c$
      exact absurd (mul_left_cancel (hcs231.trans hc.symm.symm)) (hbe.symm)
    · -- $a \diamond e = d$
      rcases hspan (a * c) with hcs297 | hcs297 | hcs297 | hcs297 | hcs297 | hcs297
      · -- $a \diamond c = a$
        exact absurd (mul_left_cancel (hcs297.trans (hidem a).eq.symm)) (hac.symm)
      · -- $a \diamond c = b$
        have hv298 : a * f = e := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs297.symm)) (hcf.symm)
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs231.symm)) (hef.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
        rcases hspan (d * a) with hcs299 | hcs299 | hcs299 | hcs299 | hcs299 | hcs299
        · -- $d \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs299) (had.symm)
        · -- $d \diamond a = b$
          have hv300 : e * b = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs299))).symm.trans
              (eq677 e a)).trans hv298.symm)
          rcases hspan (e * a) with hcs301 | hcs301 | hcs301 | hcs301 | hcs301 | hcs301
          · -- $e \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs301) (hae.symm)
          · -- $e \diamond a = b$
            have hv302 : f * b = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
                ((congrArg (· * a) hv298).trans hcs301))).symm.trans
                (eq677 f a)).trans hcs1.symm)
            rcases hspan (f * e) with hcs303 | hcs303 | hcs303 | hcs303 | hcs303 | hcs303
            · -- $f \diamond e = a$
              have hdv1 : f / e = b := div_eq_iff_mul_eq.mpr hv300
              have hdv2 : f / e / e = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs301
              have hik : IsIdempotentElem (f / e / e) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs303.trans hdv2.symm)) (hef.symm)
            · -- $f \diamond e = b$
              have hdv : f / e = b := div_eq_iff_mul_eq.mpr hv300
              have hik : IsIdempotentElem (f / e) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs303.trans hdv.symm)) (hef.symm)
            · -- $f \diamond e = c$
              have hv304 : b * c = a :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (b * ·)
                  ((congrArg (· * e) hv300).trans hcs303))).symm.trans
                  (eq677 b e)).trans hcs301.symm)
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hv304
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $f \diamond e = d$
              exact absurd (mul_left_cancel (hcs303.trans hv302.symm)) (hbe.symm)
            · -- $f \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs303) (hef.symm)
            · -- $f \diamond e = f$
              exact absurd (mul_left_cancel (hcs303.trans (hidem f).eq.symm)) hef
          · -- $e \diamond a = c$
            have hv305 : f * c = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
                ((congrArg (· * a) hv298).trans hcs301))).symm.trans
                (eq677 f a)).trans hcs1.symm)
            rcases hspan (d * f) with hcs306 | hcs306 | hcs306 | hcs306 | hcs306 | hcs306
            · -- $d \diamond f = a$
              have hdv : a / d = f := div_eq_iff_mul_eq.mpr hcs306
              have hik : IsIdempotentElem (a / d) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $d \diamond f = b$
              exact absurd (mul_left_cancel (hcs306.trans hcs299.symm)) (haf.symm)
            · -- $d \diamond f = c$
              have hdv : d / f = c := div_eq_iff_mul_eq.mpr hv305
              have hik : IsIdempotentElem (d / f) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hcs306.trans hdv.symm)) hdf
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs306.trans (hidem d).eq.symm)) (hdf.symm)
            · -- $d \diamond f = e$
              have hv307 : f * a = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                  (congrArg (d * ·) (congrArg (· * a) hcs1))).symm.trans
                  (eq677 d a)).trans hcs231.symm)).trans hcs306.symm)
              exact absurd (mul_left_cancel (hv307.trans (hidem f).eq.symm)) haf
            · -- $d \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs306) hdf
          · -- $e \diamond a = d$
            have hdv1 : e / a = f := div_eq_iff_mul_eq.mpr hv298
            have hdv2 : e / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (e / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs301.trans hdv2.symm)) (hae.symm)
          · -- $e \diamond a = e$
            exact absurd (mul_left_cancel (hcs301.trans (hidem e).eq.symm)) hae
          · -- $e \diamond a = f$
            exact absurd (mul_left_cancel (hcs301.trans hv300.symm)) hab
        · -- $d \diamond a = c$
          have hv308 : e * c = f :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (e * ·)
              ((congrArg (· * a) hcs231).trans hcs299))).symm.trans
              (eq677 e a)).trans hv298.symm)
          rcases hspan (e * a) with hcs309 | hcs309 | hcs309 | hcs309 | hcs309 | hcs309
          · -- $e \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs309) (hae.symm)
          · -- $e \diamond a = b$
            have hv310 : f * b = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
                ((congrArg (· * a) hv298).trans hcs309))).symm.trans
                (eq677 f a)).trans hcs1.symm)
            rcases hspan (d * f) with hcs311 | hcs311 | hcs311 | hcs311 | hcs311 | hcs311
            · -- $d \diamond f = a$
              have hdv : a / d = f := div_eq_iff_mul_eq.mpr hcs311
              have hik : IsIdempotentElem (a / d) := hdv ▸ hidem f
              exact absurd (eq_of_mul_eq_div hik (hcs1.trans hdv.symm)) had
            · -- $d \diamond f = b$
              have hdv : d / f = b := div_eq_iff_mul_eq.mpr hv310
              have hik : IsIdempotentElem (d / f) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs311.trans hdv.symm)) hdf
            · -- $d \diamond f = c$
              exact absurd (mul_left_cancel (hcs311.trans hcs299.symm)) (haf.symm)
            · -- $d \diamond f = d$
              exact absurd (mul_left_cancel (hcs311.trans (hidem d).eq.symm)) (hdf.symm)
            · -- $d \diamond f = e$
              have hv312 : f * a = f :=
                mul_left_cancel ((mul_left_cancel (((congrArg (a * ·)
                  (congrArg (d * ·) (congrArg (· * a) hcs1))).symm.trans
                  (eq677 d a)).trans hcs231.symm)).trans hcs311.symm)
              exact absurd (mul_left_cancel (hv312.trans (hidem f).eq.symm)) haf
            · -- $d \diamond f = f$
              exact absurd (eq_of_mul_eq_self_right (hidem f) hcs311) hdf
          · -- $e \diamond a = c$
            have hv313 : f * c = d :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
                ((congrArg (· * a) hv298).trans hcs309))).symm.trans
                (eq677 f a)).trans hcs1.symm)
            rcases hspan (f * e) with hcs314 | hcs314 | hcs314 | hcs314 | hcs314 | hcs314
            · -- $f \diamond e = a$
              have hdv1 : f / e = c := div_eq_iff_mul_eq.mpr hv308
              have hdv2 : f / e / e = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs309
              have hik : IsIdempotentElem (f / e / e) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs314.trans hdv2.symm)) (hef.symm)
            · -- $f \diamond e = b$
              have hv315 : c * b = a :=
                mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                  ((congrArg (· * e) hv308).trans hcs314))).symm.trans
                  (eq677 c e)).trans hcs309.symm)
              have hdv : a / c = b := div_eq_iff_mul_eq.mpr hv315
              have hik : IsIdempotentElem (a / c) := hdv ▸ hidem b
              exact absurd (eq_of_mul_eq_div hik (hcs297.trans hdv.symm)) hac
            · -- $f \diamond e = c$
              have hdv : f / e = c := div_eq_iff_mul_eq.mpr hv308
              have hik : IsIdempotentElem (f / e) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hcs314.trans hdv.symm)) (hef.symm)
            · -- $f \diamond e = d$
              exact absurd (mul_left_cancel (hcs314.trans hv313.symm)) (hce.symm)
            · -- $f \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs314) (hef.symm)
            · -- $f \diamond e = f$
              exact absurd (mul_left_cancel (hcs314.trans (hidem f).eq.symm)) hef
          · -- $e \diamond a = d$
            have hdv1 : e / a = f := div_eq_iff_mul_eq.mpr hv298
            have hdv2 : e / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
            have hik : IsIdempotentElem (e / a / a) := hdv2 ▸ hidem d
            exact absurd (eq_of_mul_eq_div_div hik (hcs309.trans hdv2.symm)) (hae.symm)
          · -- $e \diamond a = e$
            exact absurd (mul_left_cancel (hcs309.trans (hidem e).eq.symm)) hae
          · -- $e \diamond a = f$
            exact absurd (mul_left_cancel (hcs309.trans hv308.symm)) hac
        · -- $d \diamond a = d$
          exact absurd (mul_left_cancel (hcs299.trans (hidem d).eq.symm)) had
        · -- $d \diamond a = e$
          have hdv : d / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hik : IsIdempotentElem (d / a) := hdv ▸ hidem e
          exact absurd (eq_of_mul_eq_div hik (hcs299.trans hdv.symm)) (had.symm)
        · -- $d \diamond a = f$
          have hdv1 : d / a = e := div_eq_iff_mul_eq.mpr hcs231
          have hdv2 : d / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv298
          have hik : IsIdempotentElem (d / a / a) := hdv2 ▸ hidem f
          exact absurd (eq_of_mul_eq_div_div hik (hcs299.trans hdv2.symm)) (had.symm)
      · -- $a \diamond c = c$
        exact absurd (mul_left_cancel (hcs297.trans hc.symm.symm)) (hbc.symm)
      · -- $a \diamond c = d$
        exact absurd (mul_left_cancel (hcs297.trans hcs231.symm)) hce
      · -- $a \diamond c = e$
        have hv316 : a * f = b := by
          rcases hspan (a * f) with hz | hz | hz | hz | hz | hz
          · exact absurd (mul_left_cancel (hz.trans (hidem a).eq.symm)) (haf.symm)
          · exact hz
          · exact absurd (mul_left_cancel (hz.trans hc.symm.symm)) (hbf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs231.symm)) (hef.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs297.symm)) (hcf.symm)
          · exact absurd (mul_left_cancel (hz.trans hcs1.symm)) (hdf.symm)
        rcases hspan (b * a) with hcs317 | hcs317 | hcs317 | hcs317 | hcs317 | hcs317
        · -- $b \diamond a = a$
          exact absurd (eq_of_mul_eq_self_right (hidem a) hcs317) (hab.symm)
        · -- $b \diamond a = b$
          exact absurd (mul_left_cancel (hcs317.trans (hidem b).eq.symm)) hab
        · -- $b \diamond a = c$
          have hv318 : f * c = d :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hv316).trans hcs317))).symm.trans
              (eq677 f a)).trans hcs1.symm)
          rcases hspan (c * a) with hcs319 | hcs319 | hcs319 | hcs319 | hcs319 | hcs319
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs319) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs319.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs319.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv320 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs319))).symm.trans
                (eq677 b a)).trans hv316.symm)
            rcases hspan (b * e) with hcs321 | hcs321 | hcs321 | hcs321 | hcs321 | hcs321
            · -- $b \diamond e = a$
              have hv322 : c * b = c :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                  (eq677 a b)).trans hcs321.symm)).trans hcs297.symm)
              exact absurd (mul_left_cancel (hv322.trans (hidem c).eq.symm)) hbc
            · -- $b \diamond e = b$
              exact absurd (mul_left_cancel (hcs321.trans (hidem b).eq.symm)) (hbe.symm)
            · -- $b \diamond e = c$
              exact absurd (mul_left_cancel (hcs321.trans hcs317.symm)) (hae.symm)
            · -- $b \diamond e = d$
              have e1 : b * e = a * e := hcs321.trans hcs231.symm
              have e2 : b * (a * e) = a * (a * e) := by
                rw [hcs231]
                exact hv320.trans hcs1.symm
              exact absurd (eq_of_mul_eq_of_mul_mul_eq e1 e2) (hab.symm)
            · -- $b \diamond e = e$
              exact absurd (eq_of_mul_eq_self_right (hidem e) hcs321) hbe
            · -- $b \diamond e = f$
              exact absurd (mul_left_cancel (hcs321.trans hv320.symm)) (hde.symm)
          · -- $c \diamond a = e$
            have hv323 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs319))).symm.trans
                (eq677 b a)).trans hv316.symm)
            rcases hspan (b * d) with hcs324 | hcs324 | hcs324 | hcs324 | hcs324 | hcs324
            · -- $b \diamond d = a$
              have hv325 : c * b = e :=
                mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                  (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                  (eq677 a b)).trans hcs324.symm)).trans hcs231.symm)
              exact absurd (mul_left_cancel (hv325.trans hcs319.symm)) (hab.symm)
            · -- $b \diamond d = b$
              exact absurd (mul_left_cancel (hcs324.trans (hidem b).eq.symm)) (hbd.symm)
            · -- $b \diamond d = c$
              exact absurd (mul_left_cancel (hcs324.trans hcs317.symm)) (had.symm)
            · -- $b \diamond d = d$
              exact absurd (eq_of_mul_eq_self_right (hidem d) hcs324) hbd
            · -- $b \diamond d = e$
              rcases hspan (b * c) with hcs326 | hcs326 | hcs326 | hcs326 | hcs326 | hcs326
              · -- $b \diamond c = a$
                have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs326
                have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
                exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
              · -- $b \diamond c = b$
                exact absurd (mul_left_cancel (hcs326.trans (hidem b).eq.symm)) (hbc.symm)
              · -- $b \diamond c = c$
                exact absurd (mul_left_cancel (hcs326.trans hcs317.symm)) (hac.symm)
              · -- $b \diamond c = d$
                have hv327 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs317.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs326.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs324.symm)) (hdf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv323.symm)) (hef.symm)
                have hv328 : c * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                    (eq677 a b)).trans hv327.symm)).trans hcs1.symm)
                have hv329 : b * d = f :=
                  (congrArg (b * ·) ((congrArg (f * ·) ((congrArg (· * b) hv327).trans
                    hc.symm)).trans hv318)).symm.trans (eq677 f b)
                exact absurd (hv329.symm.trans hcs324) (hef.symm)
              · -- $b \diamond c = e$
                exact absurd (mul_left_cancel (hcs326.trans hcs324.symm)) hcd
              · -- $b \diamond c = f$
                exact absurd (mul_left_cancel (hcs326.trans hv323.symm)) hce
            · -- $b \diamond d = f$
              exact absurd (mul_left_cancel (hcs324.trans hv323.symm)) hde
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv316
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs319.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = d$
          have hdv1 : b / a = f := div_eq_iff_mul_eq.mpr hv316
          have hdv2 : b / a / a = d := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs1
          have hik : IsIdempotentElem (b / a / a) := hdv2 ▸ hidem d
          exact absurd (eq_of_mul_eq_div_div hik (hcs317.trans hdv2.symm)) (hab.symm)
        · -- $b \diamond a = e$
          have hv330 : f * e = d :=
            mul_left_cancel (((congrArg (a * ·) (congrArg (f * ·)
              ((congrArg (· * a) hv316).trans hcs317))).symm.trans
              (eq677 f a)).trans hcs1.symm)
          rcases hspan (c * a) with hcs331 | hcs331 | hcs331 | hcs331 | hcs331 | hcs331
          · -- $c \diamond a = a$
            exact absurd (eq_of_mul_eq_self_right (hidem a) hcs331) (hac.symm)
          · -- $c \diamond a = b$
            have hdv : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hik : IsIdempotentElem (c / a) := hdv ▸ hidem b
            exact absurd (eq_of_mul_eq_div hik (hcs331.trans hdv.symm)) (hac.symm)
          · -- $c \diamond a = c$
            exact absurd (mul_left_cancel (hcs331.trans (hidem c).eq.symm)) hac
          · -- $c \diamond a = d$
            have hv332 : b * d = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs331))).symm.trans
                (eq677 b a)).trans hv316.symm)
            rcases hspan (b * c) with hcs333 | hcs333 | hcs333 | hcs333 | hcs333 | hcs333
            · -- $b \diamond c = a$
              have hdv : a / b = c := div_eq_iff_mul_eq.mpr hcs333
              have hik : IsIdempotentElem (a / b) := hdv ▸ hidem c
              exact absurd (eq_of_mul_eq_div hik (hc.symm.trans hdv.symm)) hab
            · -- $b \diamond c = b$
              exact absurd (mul_left_cancel (hcs333.trans (hidem b).eq.symm)) (hbc.symm)
            · -- $b \diamond c = c$
              exact absurd (eq_of_mul_eq_self_right (hidem c) hcs333) hbc
            · -- $b \diamond c = d$
              rcases hspan (b * e) with hcs334 | hcs334 | hcs334 | hcs334 | hcs334 | hcs334
              · -- $b \diamond e = a$
                have hv335 : e * b = c :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                    (eq677 a b)).trans hcs334.symm)).trans hcs297.symm)
                have hv336 : e * c = a :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                    ((congrArg (· * b) hcs334).trans hc.symm))).symm.trans
                    (eq677 e b)).trans hcs317.symm)
                have hv337 : c * d = b :=
                  mul_left_cancel (((congrArg (e * ·) (congrArg (c * ·)
                    ((congrArg (· * e) hv336).trans hcs231))).symm.trans
                    (eq677 c e)).trans hv335.symm)
                have hdv : b / c = d := div_eq_iff_mul_eq.mpr hv337
                have hik : IsIdempotentElem (b / c) := hdv ▸ hidem d
                exact absurd (eq_of_mul_eq_div hik (hcs333.trans hdv.symm)) hbc
              · -- $b \diamond e = b$
                exact absurd (mul_left_cancel (hcs334.trans (hidem b).eq.symm)) (hbe.symm)
              · -- $b \diamond e = c$
                have hv338 : b * f = a := by
                  rcases hspan (b * f) with hz | hz | hz | hz | hz | hz
                  · exact hz
                  · exact absurd (mul_left_cancel (hz.trans (hidem b).eq.symm)) (hbf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs334.symm)) (hef.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs333.symm)) (hcf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hcs317.symm)) (haf.symm)
                  · exact absurd (mul_left_cancel (hz.trans hv332.symm)) (hdf.symm)
                have hv339 : e * b = d :=
                  mul_left_cancel ((mul_left_cancel (((congrArg (b * ·)
                    (congrArg (a * ·) (congrArg (· * b) hcs317))).symm.trans
                    (eq677 a b)).trans hv338.symm)).trans hcs1.symm)
                have hv340 : f * c = d :=
                  mul_left_cancel (((congrArg (b * ·) (congrArg (f * ·)
                    ((congrArg (· * b) hv338).trans hc.symm))).symm.trans
                    (eq677 f b)).trans hv332.symm)
                exact absurd (mul_left_cancel (hv340.trans hv330.symm)) hce
              · -- $b \diamond e = d$
                exact absurd (mul_left_cancel (hcs334.trans hcs333.symm)) (hce.symm)
              · -- $b \diamond e = e$
                exact absurd (mul_left_cancel (hcs334.trans hcs317.symm)) (hae.symm)
              · -- $b \diamond e = f$
                exact absurd (mul_left_cancel (hcs334.trans hv332.symm)) (hde.symm)
            · -- $b \diamond c = e$
              exact absurd (mul_left_cancel (hcs333.trans hcs317.symm)) (hac.symm)
            · -- $b \diamond c = f$
              exact absurd (mul_left_cancel (hcs333.trans hv332.symm)) hcd
          · -- $c \diamond a = e$
            have hv341 : b * e = f :=
              mul_left_cancel (((congrArg (a * ·) (congrArg (b * ·)
                ((congrArg (· * a) hc.symm).trans hcs331))).symm.trans
                (eq677 b a)).trans hv316.symm)
            rcases hspan (f * b) with hcs342 | hcs342 | hcs342 | hcs342 | hcs342 | hcs342
            · -- $f \diamond b = a$
              have hdv1 : f / b = e := div_eq_iff_mul_eq.mpr hv341
              have hdv2 : f / b / b = a := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hcs317
              have hik : IsIdempotentElem (f / b / b) := hdv2 ▸ hidem a
              exact absurd (eq_of_mul_eq_div_div hik (hcs342.trans hdv2.symm)) (hbf.symm)
            · -- $f \diamond b = b$
              exact absurd (eq_of_mul_eq_self_right (hidem b) hcs342) (hbf.symm)
            · -- $f \diamond b = c$
              have hv343 : e * c = a :=
                mul_left_cancel (((congrArg (b * ·) (congrArg (e * ·)
                  ((congrArg (· * b) hv341).trans hcs342))).symm.trans
                  (eq677 e b)).trans hcs317.symm)
              have hdv : e / c = a := div_eq_iff_mul_eq.mpr hcs331
              have hik : IsIdempotentElem (e / c) := hdv ▸ hidem a
              exact absurd (eq_of_mul_eq_div hik (hv343.trans hdv.symm)) (hce.symm)
            · -- $f \diamond b = d$
              exact absurd (mul_left_cancel (hcs342.trans hv330.symm)) hbe
            · -- $f \diamond b = e$
              have hdv : f / b = e := div_eq_iff_mul_eq.mpr hv341
              have hik : IsIdempotentElem (f / b) := hdv ▸ hidem e
              exact absurd (eq_of_mul_eq_div hik (hcs342.trans hdv.symm)) (hbf.symm)
            · -- $f \diamond b = f$
              exact absurd (mul_left_cancel (hcs342.trans (hidem f).eq.symm)) hbf
          · -- $c \diamond a = f$
            have hdv1 : c / a = b := div_eq_iff_mul_eq.mpr hc.symm
            have hdv2 : c / a / a = f := by rw [hdv1]; exact div_eq_iff_mul_eq.mpr hv316
            have hik : IsIdempotentElem (c / a / a) := hdv2 ▸ hidem f
            exact absurd (eq_of_mul_eq_div_div hik (hcs331.trans hdv2.symm)) (hac.symm)
        · -- $b \diamond a = f$
          have hdv : b / a = f := div_eq_iff_mul_eq.mpr hv316
          have hik : IsIdempotentElem (b / a) := hdv ▸ hidem f
          exact absurd (eq_of_mul_eq_div hik (hcs317.trans hdv.symm)) (hab.symm)
      · -- $a \diamond c = f$
        exact absurd (mul_left_cancel (hcs297.trans hcs1.symm)) hcd
    · -- $a \diamond e = e$
      exact absurd (eq_of_mul_eq_self_right (hidem e) hcs231) hae
    · -- $a \diamond e = f$
      exact absurd (mul_left_cancel (hcs231.trans hcs1.symm)) (hde.symm)

/-- **No magma with six elements satisfies Equation 677.**

Every element of such a magma would be idempotent (`forall_isIdempotentElem_of_card_eq_six`, the
degree analysis), and no six-element magma satisfies Equation 677 together with the idempotent
law (`not_forall_isIdempotentElem_of_card_eq_six`). -/
theorem card_ne_six : Finite.card M ≠ 6 := fun hM =>
  not_forall_isIdempotentElem_of_card_eq_six hM (forall_isIdempotentElem_of_card_eq_six hM)

end OrderSix

/-- **No magma with six elements satisfies Equation 677**, with the carrier enumerated
explicitly: a duplicate-free list of all the elements of a magma satisfying Equation 677 never
has length six. -/
theorem no_order_six {M : Type u} [Mul M] [Magma677 M] (l : List M) (hnd : l.Nodup)
    (hall : ∀ x, x ∈ l) : l.length ≠ 6 := by
  haveI : Finite M := ⟨⟨l, hnd, hall⟩⟩
  rw [← Finite.card_eq_length hnd hall]
  exact card_ne_six

/-- **No binary operation on a six-element set satisfies Equation 677**: for every
$\diamond \colon \mathrm{Fin}\,6 \times \mathrm{Fin}\,6 \to \mathrm{Fin}\,6$ there are $x, y$ with
$x \neq y \diamond (x \diamond ((y \diamond x) \diamond y))$. -/
theorem no_op_on_fin_six (op : Fin 6 → Fin 6 → Fin 6) :
    ¬ ∀ x y : Fin 6, x = op y (op x (op (op y x) y)) := fun h =>
  @no_order_six (Fin 6) ⟨op⟩ (@Magma677.mk (Fin 6) ⟨op⟩ h) [0, 1, 2, 3, 4, 5] (by decide)
    (by decide) rfl

end Magma677
