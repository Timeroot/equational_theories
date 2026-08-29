import equational_theories.Definability.UnaryCore

/-!
# Source 336: a set with an idempotent map

`Equation336`, `x ◇ y = y ◇ (y ◇ y)`, has a right-hand side that does not mention `x`, so putting
`x := y` in it identifies the two: writing `s v := v ◇ v`, every product is `x ◇ y = s y`, and the
law itself then reads `s y = s (s y)`. **The models of `Equation336` are exactly the sets with an
idempotent map**.

So the language names `x, s x, y, s y` -- nine equality patterns, `1728` `QFOp` decision trees, all
of them `∅`-definable, which is the forward half of `StructuralOnMagma` for free. Unlike the
`s^k = id` sources the patterns can also *test* idempotency, `s x = x`, and two of the five members
below need that test.

`984` of the trees define `s` back and `648` do it on their diagonal, `y □ y = s y`, which is the
quantifier-free `Unary.definable_graph_diag`. Five settle 168 of source 336's 179 open targets:

    x □ y := if y = x then s x else x                                              (`t72`)
    x □ y := if y = x then s x else if y = s x then x else y                       (`t1546`)
    x □ y := if s y = y then x else if s x = x then y else s x                     (`t1093`)
    x □ y := if s y = y then y else if s x = x then y else s x                     (`t1569`)
    x □ y := if y = x then s x else if s y = x then y else x                       (`t936`)

The generated proofs live in `Unary336_*.lean`.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

namespace Unary336

variable {G : Type} (M : Magma G)

/-! ## The normal form -/

/-- Every product is `s` of its right argument. -/
theorem sop (h336 : Equation336 G) (a b : G) : M.op a b = M.op b b :=
  (h336 a b).trans (h336 b b).symm

/-- `s` is idempotent. -/
theorem sidem (h336 : Equation336 G) (v : G) :
    M.op (M.op v v) (M.op v v) = M.op v v := by
  have h := h336 v v
  rw [sop M h336 v (M.op v v)] at h
  exact h.symm

theorem name_s (h336 : Equation336 G) :
    ∃ s : G → G, (∀ u v : G, M.op u v = s v) ∧ (∀ v : G, s (s v) = s v) :=
  ⟨fun v ↦ M.op v v, sop M h336, sidem M h336⟩

/-! ## The operations -/

/-- `x □ y := if y = x then s x else x`. -/
def t72 : QFOp := .ite (Lf 1) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0)) (.leaf (Lf 0))

/-- `x □ y := if y = x then s x else if y = s x then x else y`. -/
def t1546 : QFOp :=
  .ite (Lf 1) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0))
    (.ite (Lf 1) (Lf 0 ⋆ Lf 0) (.leaf (Lf 0)) (.leaf (Lf 1)))

/-- `x □ y := if s y = y then x else if s x = x then y else s x`. -/
def t1093 : QFOp :=
  .ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 0))
    (.ite (Lf 0 ⋆ Lf 0) (Lf 0) (.leaf (Lf 1)) (.leaf (Lf 0 ⋆ Lf 0)))

/-- `x □ y := if s y = y then y else if s x = x then y else s x`. -/
def t1569 : QFOp :=
  .ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 1))
    (.ite (Lf 0 ⋆ Lf 0) (Lf 0) (.leaf (Lf 1)) (.leaf (Lf 0 ⋆ Lf 0)))

/-- `x □ y := if y = x then s x else if s y = x then y else x`. -/
def t936 : QFOp :=
  .ite (Lf 1) (Lf 0) (.leaf (Lf 0 ⋆ Lf 0))
    (.ite (Lf 1 ⋆ Lf 1) (Lf 0) (.leaf (Lf 1)) (.leaf (Lf 0)))

open scoped Classical in
theorem t72_apply (a b : G) :
    (t72.magma M).op a b = if b = a then M.op a a else a := by
  show @QFOp.eval _ M t72 ![a, b] = _
  simp only [t72, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t1546_apply (a b : G) :
    (t1546.magma M).op a b =
      if b = a then M.op a a else if b = M.op a a then a else b := by
  show @QFOp.eval _ M t1546 ![a, b] = _
  simp only [t1546, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t1093_apply (a b : G) :
    (t1093.magma M).op a b =
      if M.op b b = b then a else if M.op a a = a then b else M.op a a := by
  show @QFOp.eval _ M t1093 ![a, b] = _
  simp only [t1093, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t1569_apply (a b : G) :
    (t1569.magma M).op a b =
      if M.op b b = b then b else if M.op a a = a then b else M.op a a := by
  show @QFOp.eval _ M t1569 ![a, b] = _
  simp only [t1569, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
theorem t936_apply (a b : G) :
    (t936.magma M).op a b =
      if b = a then M.op a a else if M.op b b = a then b else a := by
  show @QFOp.eval _ M t936 ![a, b] = _
  simp only [t936, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## The diagonals name `s`

The two trees that branch on `s x = x` return `x` on that branch, which is `s x` exactly because
the branch says so; no hypothesis on the source is needed anywhere here. -/

theorem t72_diag (y : G) : (t72.magma M).op y y = M.op y y := by
  classical simp [t72_apply M y y]

theorem t1546_diag (y : G) : (t1546.magma M).op y y = M.op y y := by
  classical simp [t1546_apply M y y]

theorem t1093_diag (y : G) : (t1093.magma M).op y y = M.op y y := by
  classical grind [t1093_apply M y y]

theorem t1569_diag (y : G) : (t1569.magma M).op y y = M.op y y := by
  classical grind [t1569_apply M y y]

theorem t936_diag (y : G) : (t936.magma M).op y y = M.op y y := by
  classical simp [t936_apply M y y]

end Unary336
