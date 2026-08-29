import equational_theories.Definability.CaseSplit
import equational_theories.Equations.All

/-!
# Source 41: the constant magma, defined into by cases

`Equation41`, `x ◇ x = y ◇ z`, says every product equals every other, so its models are exactly
the **constant magmas** `x ◇ y = c`. That makes it the poorest source there is for term arguments:
`Definability/Constant.lean` shows the clone is `{π₁, π₂, const c}`, three operations, so almost
nothing is term-definable from it. It is also invisible to the exact-`Aut` device, whose rectangle
for `Aut(const c) = S_{n-1}` is carrier-independent and long spent.

Plain definability is a different matter, because a formula may branch on equalities. The only
element the language can name is `c` -- it is `x ◇ x` for any `x` -- so a `∅`-definable binary
operation has `M'(x, y) ∈ {c, x, y}` and may choose only on the pattern of `(x = c, y = c, x = y)`.
Five patterns are realisable, giving exactly `1 * 2 * 2 * 2 * 3 = 24` operations. Five of them,
below, settle 178 of source 41's 188 open targets.

Each is a `QFOp` decision tree, so the forward half of `StructuralOnMagma` is
`QFOp.definable_graph`. The reverse half is what makes these *structural* rather than merely
definable, and it is uniform: all five have `z □ z = c` for every `z`, so `M.Graph`, which is
`{v | v none = c}`, is the quantifier-free `z = z □ z`.

Nothing here needs a finite carrier. A term of `□` evaluated at `σ` stays inside `{c} ∪ image σ`,
so these are genuine `StructuralFrom` facts, the strongest flavour on the board.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

namespace Const41

variable {G : Type}

/-! ## The five trees

The test `y ◇ y = y` is `y = c`, because `y ◇ y` *is* `c`; the leaf `x ◇ x` is `c` itself. -/

/-- `x □ y := if y = c then x else c`. -/
def t6 : QFOp := .ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 0)) (.leaf (Lf 0 ⋆ Lf 0))

/-- `x □ y := if x = c then y else c`. -/
def t12 : QFOp := .ite (Lf 0 ⋆ Lf 0) (Lf 0) (.leaf (Lf 1)) (.leaf (Lf 0 ⋆ Lf 0))

/-- `x □ y := if x = c then y else if y = c then x else c`. -/
def t18 : QFOp :=
  .ite (Lf 0 ⋆ Lf 0) (Lf 0) (.leaf (Lf 1))
    (.ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 0)) (.leaf (Lf 0 ⋆ Lf 0)))

/-- `x □ y := if x = c then y else if y = c then x else if x = y then c else x`. -/
def t19 : QFOp :=
  .ite (Lf 0 ⋆ Lf 0) (Lf 0) (.leaf (Lf 1))
    (.ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 0))
      (.ite (Lf 0) (Lf 1) (.leaf (Lf 0 ⋆ Lf 0)) (.leaf (Lf 0))))

/-- `x □ y := if x = c then y else if y = c then x else if x = y then c else y`. -/
def t20 : QFOp :=
  .ite (Lf 0 ⋆ Lf 0) (Lf 0) (.leaf (Lf 1))
    (.ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 0))
      (.ite (Lf 0) (Lf 1) (.leaf (Lf 0 ⋆ Lf 0)) (.leaf (Lf 1))))

/-! ## Reading the trees on a constant magma -/

open scoped Classical in
theorem t6_apply (M : Magma G) (c a b : G) (hc : ∀ u v : G, M.op u v = c) :
    (t6.magma M).op a b = if b = c then a else c := by
  show @QFOp.eval _ M t6 ![a, b] = _
  simp only [t6, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  rcases eq_or_ne b c with h | h
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

open scoped Classical in
theorem t12_apply (M : Magma G) (c a b : G) (hc : ∀ u v : G, M.op u v = c) :
    (t12.magma M).op a b = if a = c then b else c := by
  show @QFOp.eval _ M t12 ![a, b] = _
  simp only [t12, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  rcases eq_or_ne a c with h | h
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

open scoped Classical in
theorem t18_apply (M : Magma G) (c a b : G) (hc : ∀ u v : G, M.op u v = c) :
    (t18.magma M).op a b = if a = c then b else if b = c then a else c := by
  show @QFOp.eval _ M t18 ![a, b] = _
  simp only [t18, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  rcases eq_or_ne a c with h | h
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]
    rcases eq_or_ne b c with h' | h'
    · rw [if_pos h'.symm, if_pos h']
    · rw [if_neg (Ne.symm h'), if_neg h']

open scoped Classical in
theorem t19_apply (M : Magma G) (c a b : G) (hc : ∀ u v : G, M.op u v = c) :
    (t19.magma M).op a b =
      if a = c then b else if b = c then a else if a = b then c else a := by
  show @QFOp.eval _ M t19 ![a, b] = _
  simp only [t19, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  rcases eq_or_ne a c with h | h
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]
    rcases eq_or_ne b c with h' | h'
    · rw [if_pos h'.symm, if_pos h']
    · rw [if_neg (Ne.symm h'), if_neg h']

open scoped Classical in
theorem t20_apply (M : Magma G) (c a b : G) (hc : ∀ u v : G, M.op u v = c) :
    (t20.magma M).op a b =
      if a = c then b else if b = c then a else if a = b then c else b := by
  show @QFOp.eval _ M t20 ![a, b] = _
  simp only [t20, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  rcases eq_or_ne a c with h | h
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]
    rcases eq_or_ne b c with h' | h'
    · rw [if_pos h'.symm, if_pos h']
    · rw [if_neg (Ne.symm h'), if_neg h']

/-! ## The reverse definition

Each of the five trees has `z □ z = c` for every `z`, and `c` *is* the source operation, so the
source is recovered from the defined one by the one-node tree `x ◇ y := x □ x` -- no branch and no
quantifier. Running `QFOp.definable_graph` on the defined magma is then the whole proof, which is
why nothing here needs the carrier to be nonempty. -/

/-- `x ◇ y := x □ x`, the tree that reads the source constant back off the defined operation. -/
def back : QFOp := .leaf (Lf 0 ⋆ Lf 0)

theorem back_magma (N : Magma G) (a b : G) : (back.magma N).op a b = N.op a a := rfl

/-- If the tree squares everything to the source constant, the source graph is definable. -/
theorem definable_graph_rev {N : Magma G} (M : Magma G) (hd : ∀ a b : G, N.op a a = M.op a b) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage N.FOStructure _ M.Graph := by
  have hM : back.magma N = M := by
    obtain ⟨f⟩ := M
    exact congrArg Magma.mk (funext fun a ↦ funext fun b ↦ hd a b)
  rw [← hM]
  exact QFOp.definable_graph N back

/-- The source constant, extracted from `Equation41` at a point of the carrier. -/
theorem const_of_41 (M : Magma G) (h41 : Equation41 G) (a b : G) (u v : G) :
    M.op u v = M.op a b := (h41 u u v).symm.trans (h41 u a b)

open scoped Classical in
theorem t6_diag (M : Magma G) (h41 : Equation41 G) (a b : G) :
    (t6.magma M).op a a = M.op a b := by
  obtain ⟨c, hc⟩ : ∃ c : G, ∀ u v : G, M.op u v = c := ⟨M.op a b, const_of_41 M h41 a b⟩
  rw [t6_apply M c a a hc, hc a b]
  split_ifs <;> simp_all

open scoped Classical in
theorem t12_diag (M : Magma G) (h41 : Equation41 G) (a b : G) :
    (t12.magma M).op a a = M.op a b := by
  obtain ⟨c, hc⟩ : ∃ c : G, ∀ u v : G, M.op u v = c := ⟨M.op a b, const_of_41 M h41 a b⟩
  rw [t12_apply M c a a hc, hc a b]
  split_ifs <;> simp_all

open scoped Classical in
theorem t18_diag (M : Magma G) (h41 : Equation41 G) (a b : G) :
    (t18.magma M).op a a = M.op a b := by
  obtain ⟨c, hc⟩ : ∃ c : G, ∀ u v : G, M.op u v = c := ⟨M.op a b, const_of_41 M h41 a b⟩
  rw [t18_apply M c a a hc, hc a b]
  split_ifs <;> simp_all

open scoped Classical in
theorem t19_diag (M : Magma G) (h41 : Equation41 G) (a b : G) :
    (t19.magma M).op a a = M.op a b := by
  obtain ⟨c, hc⟩ : ∃ c : G, ∀ u v : G, M.op u v = c := ⟨M.op a b, const_of_41 M h41 a b⟩
  rw [t19_apply M c a a hc, hc a b]
  split_ifs <;> simp_all

open scoped Classical in
theorem t20_diag (M : Magma G) (h41 : Equation41 G) (a b : G) :
    (t20.magma M).op a a = M.op a b := by
  obtain ⟨c, hc⟩ : ∃ c : G, ∀ u v : G, M.op u v = c := ⟨M.op a b, const_of_41 M h41 a b⟩
  rw [t20_apply M c a a hc, hc a b]
  split_ifs <;> simp_all

/-- Glue: a tree that squares to the source constant and satisfies `L` witnesses
`L.StructuralOnMagma M`, both definitions at once. -/
theorem structuralOn_of_diag {β : Type*} {L : Law.MagmaLaw β} (M : Magma G) (q : QFOp)
    (hdiag : ∀ a b : G, (q.magma M).op a a = M.op a b)
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_rev M hdiag⟩

end Const41

/-! The generated `StructuralFrom Law41` theorems live in `Definability/Const41_*.lean`; the
shape of each is

    intro G M hM
    have h41 : Equation41 G := Law41.models_iff.mp hM
    refine structuralOn_of_diag M t6 (t6_diag M h41) ?_
    rw [@Law10.models_iff]
    intro x y
    obtain ⟨c, hc⟩ : ∃ c : G, ∀ u v : G, M.op u v = c := ⟨M.op x x, const_of_41 M h41 x x⟩
    simp only [t6_apply M c _ _ hc]
    split_ifs <;> simp_all

The constant is `obtain`ed rather than named by `set`: as the definitional equation `c = M.op x x`
it is a rewrite rule that sends `simp_all` around `a`, `a ◇ b`, `(a ◇ b) ◇ b`, and it never
returns. -/
