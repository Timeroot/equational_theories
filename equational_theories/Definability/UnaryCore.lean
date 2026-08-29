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

end Unary
