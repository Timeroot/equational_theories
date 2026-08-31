import equational_theories.Definability.Quad4274

/-!
# The row-image-constant family: a region that is a relation

Equation `4268` is `x ◇ (x ◇ x) = x ◇ (x ◇ y)`: the left translation `L x` is constant on its own
image.  Writing `A x := im (L x)` and `c x := x ◇ (x ◇ x)`, a model is exactly

* for each `x` a subset `A x ⊆ G` and a point `c x ∈ A x`,
* `x ◇ y = c x` for `y ∈ A x`, and a completely free `f x : G ∖ A x → A x` otherwise,

subject only to `{c x} ∪ im (f x) = A x`, which is what makes `A x` the image of the row.

This is `Definability/Quad4374.lean` with the forced region turned on its side.  There the region
was a set of *columns*, `T = im ◇`, and the value it carried was the word `y ◇ y`; here it is the
two-variable relation `y ∈ A x`, and the value it carries, `c x`, depends on the row.  Both changes
cost something.  The region is no longer a unary test, so `Quad4274.EOp` cannot express it and the
decision trees of this file carry their own; and the constant is no longer read off the region's
own element, so the reverse formula has to name it from the row.

Neither is expensive, and neither needs its own first-order formula.  A reverse read of a companion
`□` is a decision tree over the same tests, only evaluated in `□` instead of in `◇`; so both halves
of `StructuralOnMagma` are instances of one lemma, `structuralOn_tree`, applied to a pair of trees
`(q, w)` -- `q` builds the companion out of the source, `w` builds the source back out of the
companion -- and an operation costs nothing but the proof that `w` inverts `q`.

`4268` and its dual `4587` are the largest hub left on the `structural`/`all` board: 41 open
sources and 51,880 cells that the `4374`, `4351`, `4341` and `4274` devices cannot see.

## Main results

* `Quad4268.RTst`, `Quad4268.ROp`: decision trees whose tests may name a row.
* `Quad4268.ROp.definable_graph`: a tree has a definable graph, in whatever magma it is read.
* `Quad4268.GKer`, `Quad4268.gkernel`: the structure of a model of `4268`, read off the law.
* `Quad4268.structuralOn_tree`: both halves, from a tree and an inverse tree.
* `Quad4268.wRow`, `Quad4268.wIdy`: the two reverse reads the screen needs.
* `Quad4268.structural_q608`, `q633`, `q10713`, `q30848`: the four operations it picked.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma Quad4274

universe u

variable {G : Type}

namespace Quad4268

/-- The `MagmaLanguage` structure of the ambient magma, as an instance. -/
local instance instFOStructure [M : Magma G] : MagmaLanguage.Structure G := M.FOStructure

/-! ### Trees with a row test -/

/-- `∃ z, a ◇ z = b`: the word `b` lies in the row of the word `a`.  One binder, and the only test
of this file that `Quad4274.Tst` cannot state: `memFormula` quantifies over both arguments, and a
row fixes the first. -/
def rowFormula (G : Type) (a b : FreeMagma (Fin 2)) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex
    (Term.bdEqual (ap G ((a.toTerm₂ G).relabel Sum.inl) (Term.var (Sum.inr 0)))
      ((b.toTerm₂ G).relabel Sum.inl))

@[simp] theorem realize_rowFormula [M : Magma G] (a b : FreeMagma (Fin 2))
    (v : Option (Fin 2) → G) :
    (rowFormula G a b).Realize v ↔ ∃ z : G, M.op (a ⬝ (v ∘ some)) z = b ⬝ (v ∘ some) := by
  simp only [rowFormula, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_bdEqual, realize_ap, Term.realize_var, Term.realize_relabel,
    Sum.elim_comp_inl, FreeMagma.realize_toTerm₂]
  constructor
  · rintro ⟨z, h⟩; exact ⟨_, h⟩
  · rintro ⟨z, h⟩; exact ⟨z, by simpa [Fin.snoc] using h⟩

/-- A test in a decision tree of this file: an equation between words, or a row membership. -/
inductive RTst : Type
  | eq (a b : FreeMagma (Fin 2)) : RTst
  | row (a b : FreeMagma (Fin 2)) : RTst

/-- A binary operation described as a decision tree whose tests are `RTst`s. -/
inductive ROp : Type
  | leaf (t : FreeMagma (Fin 2)) : ROp
  | ite (c : RTst) (pos neg : ROp) : ROp

/-- What a test says on an assignment. -/
def RTst.holds [M : Magma G] : RTst → (Fin 2 → G) → Prop
  | .eq a b, σ => a ⬝ σ = b ⬝ σ
  | .row a b, σ => ∃ z : G, M.op (a ⬝ σ) z = b ⬝ σ

/-- The test as a formula in the argument variables `some 0`, `some 1`. -/
def RTst.toFormula (G : Type) : RTst → (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))
  | .eq a b => Term.equal (a.toTerm₂ G) (b.toTerm₂ G)
  | .row a b => rowFormula G a b

theorem RTst.realize_toFormula [Magma G] (c : RTst) (v : Option (Fin 2) → G) :
    (c.toFormula G).Realize v ↔ c.holds (v ∘ some) := by
  cases c with
  | eq a b => simp [RTst.toFormula, RTst.holds, Formula.realize_equal]
  | row a b => simp [RTst.toFormula, RTst.holds]

open scoped Classical in
/-- The operation the tree describes. -/
noncomputable def ROp.eval [Magma G] : ROp → (Fin 2 → G) → G
  | .leaf t, σ => t ⬝ σ
  | .ite c p n, σ => if c.holds σ then p.eval σ else n.eval σ

/-- The tree as a formula, in the output variable `none` and the arguments `some 0`, `some 1`. -/
def ROp.toFormula (G : Type) :
    ROp → (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))
  | .leaf t => Term.equal (var none) (t.toTerm₂ G)
  | .ite c p n => (c.toFormula G ⊓ p.toFormula G) ⊔ (∼(c.toFormula G) ⊓ n.toFormula G)

theorem ROp.realize_toFormula [Magma G] (q : ROp) (v : Option (Fin 2) → G) :
    (q.toFormula G).Realize v ↔ v none = q.eval (v ∘ some) := by
  classical
  induction q with
  | leaf t => simp [toFormula, eval, Formula.realize_equal]
  | ite c p n ihp ihn =>
    simp only [toFormula, eval, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      RTst.realize_toFormula, ihp, ihn]
    by_cases h : c.holds (v ∘ some) <;> simp [h]

/-- The magma the tree describes. -/
@[implicit_reducible]
noncomputable def ROp.magma (M : Magma G) (q : ROp) : Magma G :=
  ⟨fun x y ↦ @ROp.eval _ M q ![x, y]⟩

/-- **The graph of a tree is definable.** A decision tree over word equations and row tests is a
boolean combination of formulas of the magma language, so its graph is definable in whatever magma
the tree is read in -- which is what makes the reverse half free. -/
theorem ROp.definable_graph (M : Magma G) (q : ROp) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ (q.magma M).Graph := by
  refine ⟨q.toFormula G, Set.ext fun v ↦ ?_⟩
  have hv : ![(v ∘ some) 0, (v ∘ some) 1] = (v ∘ some) := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  show @ROp.eval _ M q ![(v ∘ some) 0, (v ∘ some) 1] = v none ↔ _
  rw [hv]
  exact eq_comm.trans (@ROp.realize_toFormula _ M q v).symm

/-! ### The structure of a model of `4268` -/

/-- The data a model of `4268` amounts to: the region `a`, which is the row relation `y ∈ A x`, and
the one fact that says the operation is the row constant there.  There is no constant to carry,
because `c x` is the word `x ◇ (x ◇ x)`. -/
structure GKer (M : Magma G) where
  /-- the row relation: `a x y` says `y` is in the image of the left translation by `x` -/
  a : G → G → Prop
  /-- every product is in the row of its left argument -/
  aim : ∀ x y : G, a x (M.op x y)
  /-- and conversely -/
  aex : ∀ x y : G, a x y → ∃ z : G, M.op x z = y
  /-- on its own row the left translation is constant, with value `c x` -/
  hin : ∀ x y : G, a x y → M.op x y = M.op x (M.op x x)

/-- Reading the kernel off the law. -/
def gkernel (M : Magma G) (h : ∀ x y : G, M.op x (M.op x x) = M.op x (M.op x y)) : GKer M where
  a x y := ∃ z : G, M.op x z = y
  aim x y := ⟨y, rfl⟩
  aex _ _ hy := hy
  hin x _ := by rintro ⟨z, rfl⟩; exact (h x z).symm

/-! ### Packaging

A pair of trees is all an operation is.  `q` is read in the source and builds the companion; `w` is
read in the companion and has to build the source back.  Both graphs are then definable by
`ROp.definable_graph`, the first over the source and the second over the companion, and the only
thing to check is that `w` really does invert `q` -- pointwise on the operation, which is enough
because a magma's graph is determined by its operation. -/

section Ops

variable (M : Magma G) (K : GKer M)

/-- The region is the row relation, as a rewrite for the `apply` lemmas. -/
theorem grow (x y : G) : (∃ z : G, M.op x z = y) ↔ K.a x y :=
  ⟨fun ⟨z, e⟩ ↦ e ▸ K.aim x z, K.aex x y⟩

/-- The rows of the new operation are the rows of the old one. -/
theorem gker_row {P : Magma G}
    (hle : ∀ x y : G, K.a x (P.op x y))
    (hsur : ∀ x y : G, K.a x y → ∃ z : G, P.op x z = y) (x y : G) :
    (∃ z : G, P.op x z = y) ↔ K.a x y :=
  ⟨fun ⟨z, e⟩ ↦ e ▸ hle x z, hsur x y⟩

/-- **Both halves of `StructuralOnMagma`, from a tree and an inverse tree.** -/
theorem structuralOn_tree (q w : ROp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hw : ∀ a b : G, @ROp.eval _ (q.magma M) w ![a, b] = M.op a b) :
    L.StructuralOnMagma M := by
  refine ⟨q.magma M, hL, ROp.definable_graph M q, ?_⟩
  have hG : (w.magma (q.magma M)).Graph = M.Graph := by
    ext v
    show @ROp.eval _ (q.magma M) w ![(v ∘ some) 0, (v ∘ some) 1] = v none ↔
      M.op ((v ∘ some) 0) ((v ∘ some) 1) = v none
    rw [hw]
  exact hG ▸ ROp.definable_graph (q.magma M) w

end Ops

/-! ### The two reverse reads

Fifty thousand region rewrites survive the model census, eleven hundred of them have a region the
companion can name, and thirty-six can also name the row constant.  Between them those thirty-six
use only two reverse trees.

`wRow` is the short one: the companion keeps the source's rows, so the region is `∃ d, x □ d = y`
and the constant is the word `x □ (x □ x)`.  `wIdy` is for the operations that break that -- their
companion's row constant is *not* a word, because the row of `x` under `□` can miss `c x` -- and it
recovers the constant by a case split before naming the region, so that in each branch the constant
is a word again and the region test `y = ĉ x` is an equation between words. -/

/-- The reverse read shared by `10713` and `30848`: the companion's own row constant on the
companion's own row, the companion off it. -/
def wRow : ROp :=
  .ite (.row (Lf 0) (Lf 1)) (.leaf (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) (.leaf (Lf 0 ⋆ Lf 1))

/-- One branch of `wIdy`, with the row constant already named by the word `t`. -/
def wBlk (t : FreeMagma (Fin 2)) : ROp :=
  .ite (.eq (Lf 0 ⋆ Lf 1) (Lf 1)) (.leaf t)
    (.ite (.eq (Lf 1) t) (.leaf t) (.leaf (Lf 0 ⋆ Lf 1)))

/-- The reverse read shared by `608` and `633`: `x □ (x □ x)` is the row constant unless it is `x`,
in which case one more step is needed, and the region is `x □ y = y ∨ y = ĉ x`. -/
def wIdy : ROp :=
  .ite (.eq (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)) (Lf 0))
    (wBlk (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))))
    (wBlk (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))

section Reverse

variable (M : Magma G) (K : GKer M) {P : Magma G}

include K in
/-- `wRow` inverts any companion with the same rows and the same row constant. -/
theorem eval_wRow
    (hle : ∀ x y : G, K.a x (P.op x y))
    (hsur : ∀ x y : G, K.a x y → ∃ z : G, P.op x z = y)
    (hc : ∀ x : G, P.op x (P.op x x) = M.op x (M.op x x))
    (hout : ∀ x y : G, ¬ K.a x y → P.op x y = M.op x y) (a b : G) :
    @ROp.eval _ P wRow ![a, b] = M.op a b := by
  classical
  simp only [wRow, ROp.eval, RTst.holds, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one,
    gker_row M K hle hsur]
  split_ifs with h
  · rw [hc a]; exact (K.hin a b h).symm
  · exact hout a b h

open scoped Classical in
omit K in
/-- `wIdy` inverts any companion whose by-cases row constant is `c x` and whose region
`x □ y = y ∨ y = c x` is exactly where the source is constant. -/
theorem eval_wIdy
    (hc : ∀ x : G, (if P.op x (P.op x x) = x then P.op x (P.op x (P.op x x))
                    else P.op x (P.op x x)) = M.op x (M.op x x))
    (hreg : ∀ x y : G, P.op x y = y ∨ y = M.op x (M.op x x) → M.op x y = M.op x (M.op x x))
    (hout : ∀ x y : G, ¬(P.op x y = y ∨ y = M.op x (M.op x x)) → P.op x y = M.op x y)
    (a b : G) :
    @ROp.eval _ P wIdy ![a, b] = M.op a b := by
  classical
  have h := hc a
  simp only [wIdy, wBlk, ROp.eval, RTst.holds, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  by_cases h1 : P.op a (P.op a a) = a
  · rw [if_pos h1] at h ⊢
    rw [h]
    split_ifs with h2 h3
    · exact (hreg a b (Or.inl h2)).symm
    · exact (hreg a b (Or.inr h3)).symm
    · exact hout a b (not_or.mpr ⟨h2, h3⟩)
  · rw [if_neg h1] at h ⊢
    rw [h]
    split_ifs with h2 h3
    · exact (hreg a b (Or.inl h2)).symm
    · exact (hreg a b (Or.inr h3)).symm
    · exact hout a b (not_or.mpr ⟨h2, h3⟩)

end Reverse

/-! ### The four operations the screen picked

Each is the source with one or two cells of each row rewritten, and each is written as a tree over
the tests `x = c x`, `y = c x` and `y ∈ A x`.

* `10713` returns the second argument on the rows of the idempotents.
* `608` returns the first argument at `y = c x`, off those rows.
* `30848` returns `x ◇ x` at `y = c x`, off those rows.
* `633` does what `10713` and `608` do, each where the other is silent. -/

section Q

variable (M : Magma G) (K : GKer M)

include K in
/-- Two facts about `c x` that every read-back argument needs: it is in the row, and the row is
constant there. -/
theorem cfix (a : G) : M.op a (M.op a (M.op a a)) = M.op a (M.op a a) :=
  K.hin a (M.op a (M.op a a)) (K.aim a (M.op a a))

/-! #### `10713`: the second argument, on the rows of the idempotents -/

/-- The tree of operation `10713`: `x □ y = y` when `y ∈ A x` and `x = c x`, else `x ◇ y`. -/
def q10713 : ROp :=
  .ite (.row (Lf 0) (Lf 1))
    (.ite (.eq (Lf 0) (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) (.leaf (Lf 1)) (.leaf (Lf 0 ⋆ Lf 1)))
    (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem q10713_apply (a b : G) :
    (q10713.magma M).op a b =
      if K.a a b then (if a = M.op a (M.op a a) then b else M.op a b) else M.op a b := by
  show @ROp.eval _ M q10713 ![a, b] = _
  simp only [q10713, ROp.eval, RTst.holds, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one,
    grow M K]

include K in
theorem q10713_le (a b : G) : K.a a ((q10713.magma M).op a b) := by
  classical
  rw [q10713_apply M K]
  have h2 : ∀ p q : G, K.a p (M.op p q) := K.aim
  split_ifs <;> grind

include K in
theorem q10713_sur (a b : G) (hb : K.a a b) : ∃ z : G, (q10713.magma M).op a z = b := by
  classical
  by_cases h : a = M.op a (M.op a a)
  · exact ⟨b, by rw [q10713_apply M K, if_pos hb, if_pos h]⟩
  · obtain ⟨w, hw⟩ := K.aex a b hb
    refine ⟨w, ?_⟩
    rw [q10713_apply M K]
    split_ifs <;> grind

include K in
theorem q10713_c (a : G) :
    (q10713.magma M).op a ((q10713.magma M).op a a) = M.op a (M.op a a) := by
  classical
  have h1 : K.a a (M.op a a) := K.aim a a
  have h2 : K.a a (M.op a (M.op a a)) := K.aim a (M.op a a)
  have h3 : ∀ p q : G, K.a p q → M.op p q = M.op p (M.op p p) := K.hin
  simp only [q10713_apply M K]
  split_ifs <;> grind

include K in
theorem q10713_out (a b : G) (hb : ¬ K.a a b) : (q10713.magma M).op a b = M.op a b := by
  classical
  rw [q10713_apply M K, if_neg hb]

include K in
/-- The whole of `StructuralOnMagma` for operation `10713`, bar the law itself. -/
theorem structural_q10713 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q10713.magma M) L) : L.StructuralOnMagma M :=
  structuralOn_tree M q10713 wRow hL
    (eval_wRow M K (q10713_le M K) (q10713_sur M K) (q10713_c M K) (q10713_out M K))

/-! #### `30848`: `x ◇ x` at `y = c x`, off the rows of the idempotents -/

/-- The tree of operation `30848`: `x □ y = x ◇ x` when `y = c x` and `x ≠ c x`, else `x ◇ y`. -/
def q30848 : ROp :=
  .ite (.eq (Lf 1) (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))
    (.ite (.eq (Lf 0) (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) (.leaf (Lf 0 ⋆ Lf 1)) (.leaf (Lf 0 ⋆ Lf 0)))
    (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem q30848_apply (a b : G) :
    (q30848.magma M).op a b =
      if b = M.op a (M.op a a) then
        (if a = M.op a (M.op a a) then M.op a b else M.op a a) else M.op a b := by
  show @ROp.eval _ M q30848 ![a, b] = _
  simp only [q30848, ROp.eval, RTst.holds, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

include K in
theorem q30848_le (a b : G) : K.a a ((q30848.magma M).op a b) := by
  classical
  rw [q30848_apply M]
  have h2 : ∀ p q : G, K.a p (M.op p q) := K.aim
  split_ifs <;> grind

include K in
theorem q30848_sur (a b : G) (hb : K.a a b) : ∃ z : G, (q30848.magma M).op a z = b := by
  classical
  have h4 := cfix M K a
  by_cases hbc : b = M.op a (M.op a a)
  · refine ⟨M.op a a, ?_⟩
    rw [q30848_apply M]
    split_ifs <;> grind
  · obtain ⟨w, hw⟩ := K.aex a b hb
    refine ⟨w, ?_⟩
    rw [q30848_apply M]
    split_ifs <;> grind

include K in
theorem q30848_c (a : G) :
    (q30848.magma M).op a ((q30848.magma M).op a a) = M.op a (M.op a a) := by
  classical
  have h4 := cfix M K a
  simp only [q30848_apply M]
  split_ifs <;> grind

include K in
theorem q30848_out (a b : G) (hb : ¬ K.a a b) : (q30848.magma M).op a b = M.op a b := by
  classical
  have h2 : K.a a (M.op a (M.op a a)) := K.aim a (M.op a a)
  rw [q30848_apply M]
  split_ifs <;> grind

include K in
/-- The whole of `StructuralOnMagma` for operation `30848`, bar the law itself. -/
theorem structural_q30848 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q30848.magma M) L) : L.StructuralOnMagma M :=
  structuralOn_tree M q30848 wRow hL
    (eval_wRow M K (q30848_le M K) (q30848_sur M K) (q30848_c M K) (q30848_out M K))

/-! #### `608`: the first argument at `y = c x`, off the rows of the idempotents -/

/-- The tree of operation `608`: `x □ y = x` when `y = c x` and `x ≠ c x`, else `x ◇ y`. -/
def q608 : ROp :=
  .ite (.eq (Lf 1) (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))
    (.ite (.eq (Lf 0) (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) (.leaf (Lf 0 ⋆ Lf 1)) (.leaf (Lf 0)))
    (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem q608_apply (a b : G) :
    (q608.magma M).op a b =
      if b = M.op a (M.op a a) then
        (if a = M.op a (M.op a a) then M.op a b else a) else M.op a b := by
  show @ROp.eval _ M q608 ![a, b] = _
  simp only [q608, ROp.eval, RTst.holds, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
include K in
theorem q608_c (a : G) :
    (if (q608.magma M).op a ((q608.magma M).op a a) = a then
        (q608.magma M).op a ((q608.magma M).op a ((q608.magma M).op a a))
      else (q608.magma M).op a ((q608.magma M).op a a)) = M.op a (M.op a a) := by
  classical
  have h4 := cfix M K a
  simp only [q608_apply M]
  split_ifs <;> grind

include K in
theorem q608_reg (a b : G)
    (h : (q608.magma M).op a b = b ∨ b = M.op a (M.op a a)) :
    M.op a b = M.op a (M.op a a) := by
  classical
  have h4 := cfix M K a
  have h2 : ∀ p q : G, K.a p (M.op p q) := K.aim
  have h3 : ∀ p q : G, K.a p q → M.op p q = M.op p (M.op p p) := K.hin
  rw [q608_apply M] at h
  split_ifs at h <;> grind

omit K in
theorem q608_out (a b : G)
    (h : ¬((q608.magma M).op a b = b ∨ b = M.op a (M.op a a))) :
    (q608.magma M).op a b = M.op a b := by
  classical
  rw [q608_apply M, if_neg (by tauto)]

include K in
/-- The whole of `StructuralOnMagma` for operation `608`, bar the law itself. -/
theorem structural_q608 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q608.magma M) L) : L.StructuralOnMagma M :=
  structuralOn_tree M q608 wIdy hL
    (eval_wIdy M (q608_c M K) (q608_reg M K) (q608_out M))

/-! #### `633`: both of the above, each where the other is silent -/

/-- The tree of operation `633`: on the rows of the idempotents it is `10713`, off them `608`. -/
def q633 : ROp :=
  .ite (.eq (Lf 0) (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))
    (.ite (.row (Lf 0) (Lf 1)) (.leaf (Lf 1)) (.leaf (Lf 0 ⋆ Lf 1)))
    (.ite (.eq (Lf 1) (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) (.leaf (Lf 0)) (.leaf (Lf 0 ⋆ Lf 1)))

open scoped Classical in
theorem q633_apply (a b : G) :
    (q633.magma M).op a b =
      if a = M.op a (M.op a a) then (if K.a a b then b else M.op a b)
      else (if b = M.op a (M.op a a) then a else M.op a b) := by
  show @ROp.eval _ M q633 ![a, b] = _
  simp only [q633, ROp.eval, RTst.holds, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one,
    grow M K]

open scoped Classical in
include K in
theorem q633_c (a : G) :
    (if (q633.magma M).op a ((q633.magma M).op a a) = a then
        (q633.magma M).op a ((q633.magma M).op a ((q633.magma M).op a a))
      else (q633.magma M).op a ((q633.magma M).op a a)) = M.op a (M.op a a) := by
  classical
  have h4 := cfix M K a
  have h2 : ∀ p q : G, K.a p (M.op p q) := K.aim
  have h3 : ∀ p q : G, K.a p q → M.op p q = M.op p (M.op p p) := K.hin
  simp only [q633_apply M K]
  split_ifs <;> grind

include K in
theorem q633_reg (a b : G)
    (h : (q633.magma M).op a b = b ∨ b = M.op a (M.op a a)) :
    M.op a b = M.op a (M.op a a) := by
  classical
  have h4 := cfix M K a
  have h2 : ∀ p q : G, K.a p (M.op p q) := K.aim
  have h3 : ∀ p q : G, K.a p q → M.op p q = M.op p (M.op p p) := K.hin
  rw [q633_apply M K] at h
  split_ifs at h <;> grind

include K in
theorem q633_out (a b : G)
    (h : ¬((q633.magma M).op a b = b ∨ b = M.op a (M.op a a))) :
    (q633.magma M).op a b = M.op a b := by
  classical
  have h2 : ∀ p q : G, K.a p (M.op p q) := K.aim
  rw [q633_apply M K] at h ⊢
  split_ifs at h ⊢ <;> grind

include K in
/-- The whole of `StructuralOnMagma` for operation `633`, bar the law itself. -/
theorem structural_q633 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q633.magma M) L) : L.StructuralOnMagma M :=
  structuralOn_tree M q633 wIdy hL
    (eval_wIdy M (q633_c M K) (q633_reg M K) (q633_out M K))

end Q

end Quad4268
