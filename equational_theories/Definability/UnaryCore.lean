import equational_theories.Definability.CaseSplit
import equational_theories.Equations.All

/-!
# Right-unary sources: the shared reverse half

A source is *right-unary* when its models are exactly the sets carrying a unary map, `x ◇ y = s y`
with `s` obeying one word identity -- `Equation13` gives `s² = id`, `Equation62` gives `s³ = id`,
and so on.  On such a magma the language names only `x, s x, .., y, s y, ..`, so a `∅`-definable
binary operation is a choice among those per equality pattern of the tuple: a `QFOp` decision tree,
and `QFOp.definable_graph` hands over the forward half of `StructuralOnMagma` for nothing.

The reverse half is the binding constraint -- `M.Graph` is the graph of `s`, so the tree has to
remember which map it was built from.  The cheapest way for it to do so is to *name* `s` on its
diagonal, `y □ y = s y`; then

    M.Graph = {(x, y, z) | z = x ◇ y} = {(x, y, z) | z = y □ y}

is an equation between `□`-terms, with no quantifier and no bound on the carrier.  That is
`definable_graph_diag` below, and it is the only part of the argument that does not depend on which
source is in play.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

-- `Term.realize` appears in the *statement* of `realize_wordOn` below, so it needs the structure
-- of the ambient magma as an instance; `CaseSplit` already has one, and the magma that matters
-- here is the one the tree describes, so every use site passes it explicitly anyway.
attribute [local instance] instFOStructure

namespace Unary

variable {G : Type} (M : Magma G) (q : QFOp)

/-- The application of `□` inside a term of the magma language. -/
private def ap (G : Type) {α : Type} (a b : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    (MagmaLanguage[[(∅ : Set G)]]).Term α :=
  Functions.apply₂ (L := MagmaLanguage[[(∅ : Set G)]]) (Sum.inl ()) a b

/-- `z = y □ y`, in the language of `□`. -/
def diagFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.bdEqual (Term.var (Sum.inl none))
    (ap G (Term.var (Sum.inl (some 1))) (Term.var (Sum.inl (some 1))))

/-- The reverse half, for a tree whose diagonal names the unary map. -/
theorem definable_graph_diag (hsop : ∀ u v : G, M.op u v = M.op v v)
    (hdiag : ∀ y : G, (q.magma M).op y y = M.op y y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  refine ⟨diagFormula G, Set.ext fun v ↦ ?_⟩
  simp only [diagFormula, ap, Formula.Realize, BoundedFormula.realize_bdEqual,
    Term.realize_functions_apply₂, Term.realize_var, Sum.elim_inl,
    Magma.FOStructure_funMap', Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Magma.Graph, Function.tupleGraph, Set.mem_setOf_eq, Function.comp_apply]
  rw [hsop (v (some 0)) (v (some 1)), ← hdiag (v (some 1))]
  exact eq_comm

/-- Glue: a tree that satisfies the target and names the unary map on its diagonal settles the
cell. -/
theorem structuralOnMagma_diag {β : Type*} {L : Law.MagmaLaw β}
    (hsop : ∀ u v : G, M.op u v = M.op v v)
    (hdiag : ∀ y : G, (q.magma M).op y y = M.op y y)
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_diag M q hsop hdiag⟩

/-! ## The mirror

A *left*-unary source has `x ◇ y = s x` instead. The tree is unchanged -- it is built from
`v ↦ v ◇ v` and equality, both of which read the same on either side -- and so is the diagonal
lemma; only the formula moves, from `z = y □ y` to `z = x □ x`. -/

/-- `z = x □ x`, in the language of `□`. -/
def ldiagFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.bdEqual (Term.var (Sum.inl none))
    (ap G (Term.var (Sum.inl (some 0))) (Term.var (Sum.inl (some 0))))

/-- The reverse half, for a left-unary source. -/
theorem definable_graph_ldiag (hlop : ∀ u v : G, M.op u v = M.op u u)
    (hdiag : ∀ y : G, (q.magma M).op y y = M.op y y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  refine ⟨ldiagFormula G, Set.ext fun v ↦ ?_⟩
  simp only [ldiagFormula, ap, Formula.Realize, BoundedFormula.realize_bdEqual,
    Term.realize_functions_apply₂, Term.realize_var, Sum.elim_inl,
    Magma.FOStructure_funMap', Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Magma.Graph, Function.tupleGraph, Set.mem_setOf_eq, Function.comp_apply]
  rw [hlop (v (some 0)) (v (some 1)), ← hdiag (v (some 0))]
  exact eq_comm

/-- Glue, for a left-unary source. -/
theorem structuralOnMagma_ldiag {β : Type*} {L : Law.MagmaLaw β}
    (hlop : ∀ u v : G, M.op u v = M.op u u)
    (hdiag : ∀ y : G, (q.magma M).op y y = M.op y y)
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_ldiag M q hlop hdiag⟩

/-! ## One square further

Some trees name not `s` but `s²` on their diagonal, and then `s` is the diagonal of the diagonal:
`(y □ y) □ (y □ y) = s y`. Still one equation, still no quantifier. -/

/-- `z = (y □ y) □ (y □ y)`, in the language of `□`. -/
def diag2Formula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.bdEqual (Term.var (Sum.inl none))
    (ap G (ap G (Term.var (Sum.inl (some 1))) (Term.var (Sum.inl (some 1))))
      (ap G (Term.var (Sum.inl (some 1))) (Term.var (Sum.inl (some 1)))))

/-- The reverse half, for a tree whose diagonal iterated twice names the unary map. -/
theorem definable_graph_diag2 (hsop : ∀ u v : G, M.op u v = M.op v v)
    (hdiag : ∀ y : G, (q.magma M).op ((q.magma M).op y y) ((q.magma M).op y y) = M.op y y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  refine ⟨diag2Formula G, Set.ext fun v ↦ ?_⟩
  simp only [diag2Formula, ap, Formula.Realize, BoundedFormula.realize_bdEqual,
    Term.realize_functions_apply₂, Term.realize_var, Sum.elim_inl,
    Magma.FOStructure_funMap', Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Magma.Graph, Function.tupleGraph, Set.mem_setOf_eq, Function.comp_apply]
  rw [hsop (v (some 0)) (v (some 1)), ← hdiag (v (some 1))]
  exact eq_comm

/-- Glue, for a tree whose diagonal names the square of the unary map. -/
theorem structuralOnMagma_diag2 {β : Type*} {L : Law.MagmaLaw β}
    (hsop : ∀ u v : G, M.op u v = M.op v v)
    (hdiag : ∀ y : G, (q.magma M).op ((q.magma M).op y y) ((q.magma M).op y y) = M.op y y)
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_diag2 M q hsop hdiag⟩

/-! ## A pair of words, and one quantifier

Naming `s` on the diagonal is the cheap shape and at the root of the family it runs out: of the
125 open targets of `Equation39` the diagonal settles 61, and for the other 64 no `□`-word at all
-- searched to six leaves -- is equal to `s y`. What does survive is a *pair* of words whose
equation cuts out, not `s y`, but the whole orbit:

    {w | u(y, w) = v(y, w)} = {y, s y}      on every model and at every `y`,

and then one universal quantifier separates the two elements: `z = s y` iff `u(y, z) = v(y, z)`,
and, in case `z = y`, that set is a singleton. `Unary13` found this shape by hand for one pair of
words; here it is for an arbitrary pair, and for either side of the source. -/

/-- A `□`-word in two variables, read over an arbitrary pair of terms. -/
def wordOn (G : Type) {α : Type} (f : Fin 2 → (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    FreeMagma (Fin 2) → (MagmaLanguage[[(∅ : Set G)]]).Term α
  | .Leaf a => f a
  | m₁ ⋆ m₂ => ap G (wordOn G f m₁) (wordOn G f m₂)

theorem realize_wordOn [N : Magma G] {α : Type} (w : α → G)
    (f : Fin 2 → (MagmaLanguage[[(∅ : Set G)]]).Term α) (t : FreeMagma (Fin 2)) :
    Term.realize w (wordOn G f t) = t ⬝ fun a ↦ Term.realize w (f a) := by
  induction t with
  | Leaf a => rfl
  | Fork m₁ m₂ ih₁ ih₂ =>
    simp only [wordOn, ap, Term.realize_functions_apply₂, Magma.FOStructure_funMap',
      evalInMagma, ih₁, ih₂]
    rfl

theorem cons_realize [Magma G] {α : Type} (w : α → G)
    (t₀ t₁ : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    (fun a ↦ Term.realize w (![t₀, t₁] a)) = ![Term.realize w t₀, Term.realize w t₁] := by
  funext a
  match a with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- `u(y, z) = v(y, z)`, and if `z = y` then `y` is the only solution: `z = s y` when the equation
cuts out the orbit `{y, s y}`. The free variable is `some i` -- `some 1` for a right-unary source
and `some 0` for a left-unary one -- and `none` is the output slot. -/
def pairFormula (G : Type) (i : Fin 2) (u v : FreeMagma (Fin 2)) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.bdEqual (wordOn G ![Term.var (Sum.inl (some i)), Term.var (Sum.inl none)] u)
      (wordOn G ![Term.var (Sum.inl (some i)), Term.var (Sum.inl none)] v) ⊓
    (Term.bdEqual (Term.var (Sum.inl none)) (Term.var (Sum.inl (some i))) ⟹
      ∀' (Term.bdEqual (wordOn G ![Term.var (Sum.inl (some i)), Term.var (Sum.inr 0)] u)
            (wordOn G ![Term.var (Sum.inl (some i)), Term.var (Sum.inr 0)] v) ⟹
          Term.bdEqual (Term.var (Sum.inr 0)) (Term.var (Sum.inl (some i)))))

theorem realize_pairFormula [N : Magma G] (i : Fin 2) (u v : FreeMagma (Fin 2))
    (w : Option (Fin 2) → G) :
    (pairFormula G i u v).Realize w ↔
      (u ⬝ ![w (some i), w none] = v ⬝ ![w (some i), w none] ∧
        (w none = w (some i) →
          ∀ z : G, u ⬝ ![w (some i), z] = v ⬝ ![w (some i), z] → z = w (some i))) := by
  have hsn : ∀ a : G, (Fin.snoc (default : Fin 0 → G) a : Fin 1 → G) 0 = a := fun _ ↦ rfl
  simp only [pairFormula, Formula.Realize, BoundedFormula.realize_inf,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, BoundedFormula.realize_bdEqual,
    realize_wordOn, cons_realize, Term.realize_var, Sum.elim_inl, Sum.elim_inr, hsn]

variable (u v : FreeMagma (Fin 2))

/-- The reverse half, for a pair of words cutting out the orbit of the right argument. -/
theorem definable_graph_pair (hsop : ∀ a b : G, M.op a b = M.op b b)
    (hpair : ∀ y z : G, @evalInMagma _ _ (q.magma M) ![y, z] u
        = @evalInMagma _ _ (q.magma M) ![y, z] v ↔ (z = y ∨ z = M.op y y)) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  refine ⟨pairFormula G 1 u v, Set.ext fun w ↦ ?_⟩
  rw [Set.mem_setOf_eq, @realize_pairFormula _ (q.magma M) 1 u v w]
  show M.op (w (some 0)) (w (some 1)) = w none ↔ _
  rw [hsop (w (some 0)) (w (some 1))]
  simp only [hpair]
  constructor
  · exact fun h ↦ ⟨Or.inr h.symm, fun h' _ hz ↦ hz.elim id fun e ↦ e.trans (h.trans h')⟩
  · rintro ⟨h | h, h2⟩
    · exact (h2 h (M.op (w (some 1)) (w (some 1))) (Or.inr rfl)).trans h.symm
    · exact h.symm

/-- The reverse half, for a left-unary source: the orbit of the *left* argument. -/
theorem definable_graph_lpair (hlop : ∀ a b : G, M.op a b = M.op a a)
    (hpair : ∀ x z : G, @evalInMagma _ _ (q.magma M) ![x, z] u
        = @evalInMagma _ _ (q.magma M) ![x, z] v ↔ (z = x ∨ z = M.op x x)) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q.magma M).FOStructure _ M.Graph := by
  refine ⟨pairFormula G 0 u v, Set.ext fun w ↦ ?_⟩
  rw [Set.mem_setOf_eq, @realize_pairFormula _ (q.magma M) 0 u v w]
  show M.op (w (some 0)) (w (some 1)) = w none ↔ _
  rw [hlop (w (some 0)) (w (some 1))]
  simp only [hpair]
  constructor
  · exact fun h ↦ ⟨Or.inr h.symm, fun h' _ hz ↦ hz.elim id fun e ↦ e.trans (h.trans h')⟩
  · rintro ⟨h | h, h2⟩
    · exact (h2 h (M.op (w (some 0)) (w (some 0))) (Or.inr rfl)).trans h.symm
    · exact h.symm

/-- Glue: a tree that satisfies the target and whose orbit equation pins the unary map settles the
cell, for a right-unary source. -/
theorem structuralOnMagma_pair {β : Type*} {L : Law.MagmaLaw β}
    (hsop : ∀ a b : G, M.op a b = M.op b b)
    (hpair : ∀ y z : G, @evalInMagma _ _ (q.magma M) ![y, z] u
        = @evalInMagma _ _ (q.magma M) ![y, z] v ↔ (z = y ∨ z = M.op y y))
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_pair M q u v hsop hpair⟩

/-- Glue, for a left-unary source. -/
theorem structuralOnMagma_lpair {β : Type*} {L : Law.MagmaLaw β}
    (hlop : ∀ a b : G, M.op a b = M.op a a)
    (hpair : ∀ x z : G, @evalInMagma _ _ (q.magma M) ![x, z] u
        = @evalInMagma _ _ (q.magma M) ![x, z] v ↔ (z = x ∨ z = M.op x x))
    (hL : @satisfies _ G (q.magma M) L) : L.StructuralOnMagma M :=
  ⟨q.magma M, hL, q.definable_graph M, definable_graph_lpair M q u v hlop hpair⟩

end Unary
