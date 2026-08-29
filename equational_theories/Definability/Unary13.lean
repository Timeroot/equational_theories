import equational_theories.Definability.CaseSplit
import equational_theories.Equations.All

/-!
# Source 13: a set with an involution

`Equation13`, `x = y ◇ (x ◇ x)`, pins its models completely. Writing `s y := y ◇ y`, the law says
`u ◇ s v = v`; so `s (s v) = v`, `s` is an involution, every element is `s` of something, and
feeding that back gives `u ◇ v = s v`. **The models of `Equation13` are exactly the sets with an
involution**, `x ◇ y = s y`, `s ∘ s = id`.

So the language names exactly `x`, `s x`, `y`, `s y`, and a `∅`-definable binary operation is a
choice of one of those four per equality pattern of the quadruple -- seven patterns, `288`
operations, all of them `QFOp` decision trees. That is the forward half of `StructuralOnMagma` for
free.

The reverse half is the binding constraint, and it kills all but one. `M.Graph` is the graph of
`s`, so the operation must remember the involution; `x □ y := s x`, say, does not (on a two-element
carrier it is the left projection whether `s` is the swap or the identity). Exactly one operation
that settles any open target survives:

    x □ y := if y = x ∨ y = x ◇ x then x else y

-- "`y`, except that inside its own `s`-orbit `x` swallows it". From it the orbit relation is
`y ∈ orbit x ↔ x □ y = x`, and then `s` is recovered with a single universal quantifier: `z = s y`
iff `z` is in `y`'s orbit and, if `z = y`, that orbit is a singleton. That is `revFormula` below.

It settles 45 of source 13's 127 open targets.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

namespace Unary13

variable {G : Type} (M : Magma G)

/-! ## The normal form -/

theorem key (h13 : Equation13 G) (u v : G) : M.op u (M.op v v) = v := (h13 v u).symm

/-- `s` is an involution. -/
theorem sinv (h13 : Equation13 G) (v : G) : M.op (M.op v v) (M.op v v) = v :=
  key M h13 (M.op v v) v

/-- Every product is `s` of its right argument. -/
theorem sop (h13 : Equation13 G) (u v : G) : M.op u v = M.op v v := by
  conv_lhs => rw [← sinv M h13 v]
  exact key M h13 u (M.op v v)

/-! ## The operation -/

/-- `x □ y := if y = x ∨ y = x ◇ x then x else y`. -/
def t : QFOp :=
  .ite (Lf 1) (Lf 0) (.leaf (Lf 0)) (.ite (Lf 1) (Lf 0 ⋆ Lf 0) (.leaf (Lf 0)) (.leaf (Lf 1)))

open scoped Classical in
theorem t_apply (a b : G) :
    (t.magma M).op a b = if b = a then a else if b = M.op a a then a else b := by
  show @QFOp.eval _ M t ![a, b] = _
  simp only [t, QFOp.eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Classical in
/-- The reading used by every generated proof: `s` written out, the two tests merged. -/
theorem t_apply' (a b : G) :
    (t.magma M).op a b = if b = a ∨ b = M.op a a then a else b := by
  rw [t_apply M a b]
  by_cases h : b = a
  · simp [h]
  · simp [h]

/-! ## Recovering the involution

`x □ y = x` says exactly that `y` lies in the `s`-orbit of `x`, and an orbit has one or two
elements, so `s y` is pinned by one universal quantifier. -/

theorem orbit (u v : G) :
    (t.magma M).op u v = u ↔ (v = u ∨ v = M.op u u) := by
  classical
  rw [t_apply' M u v]
  by_cases h : v = u ∨ v = M.op u u
  · simp [h]
  · simp only [h, iff_false]
    exact fun e ↦ h (Or.inl e)

theorem s_char (y z : G) :
    z = M.op y y ↔
      ((t.magma M).op y z = y ∧ (z = y → ∀ w : G, (t.magma M).op y w = y → w = y)) := by
  classical
  constructor
  · rintro rfl
    refine ⟨(orbit M y _).mpr (Or.inr rfl), fun he w hw ↦ ?_⟩
    rcases (orbit M y w).mp hw with rfl | rfl
    · rfl
    · exact he
  · rintro ⟨h1, h2⟩
    rcases (orbit M y z).mp h1 with he | he
    · exact he.trans (h2 he (M.op y y) ((orbit M y _).mpr (Or.inr rfl))).symm
    · exact he

/-! ## The formula -/

/-- The application of `□` inside a term of the magma language. -/
private def ap (G : Type) {α : Type} (a b : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    (MagmaLanguage[[(∅ : Set G)]]).Term α :=
  Functions.apply₂ (L := MagmaLanguage[[(∅ : Set G)]]) (Sum.inl ()) a b

/-- `z = s y`, in the language of `□`: `y □ z = y`, and if `z = y` then `y`'s orbit is a
singleton. -/
def revFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.bdEqual (ap G (Term.var (Sum.inl (some 1))) (Term.var (Sum.inl none)))
      (Term.var (Sum.inl (some 1))) ⊓
    (Term.bdEqual (Term.var (Sum.inl none)) (Term.var (Sum.inl (some 1))) ⟹
      ∀' (Term.bdEqual (ap G (Term.var (Sum.inl (some 1))) (Term.var (Sum.inr 0)))
            (Term.var (Sum.inl (some 1))) ⟹
          Term.bdEqual (Term.var (Sum.inr 0)) (Term.var (Sum.inl (some 1)))))

theorem definable_graph_rev (h13 : Equation13 G) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (t.magma M).FOStructure _ M.Graph := by
  classical
  refine ⟨revFormula G, Set.ext fun v ↦ ?_⟩
  simp only [revFormula, ap, Formula.Realize, BoundedFormula.realize_inf,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, BoundedFormula.realize_bdEqual,
    Term.realize_functions_apply₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
    Magma.FOStructure_funMap', Magma.FinArityOp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Magma.Graph, Function.tupleGraph, Set.mem_setOf_eq, Function.comp_apply]
  have hsn : ∀ a : G, (Fin.snoc (default : Fin 0 → G) a : Fin 1 → G) 0 = a := fun _ ↦ rfl
  simp only [hsn]
  rw [sop M h13 (v (some 0)) (v (some 1))]
  exact eq_comm.trans (s_char M (v (some 1)) (v none))

/-! ## Glue -/

theorem structuralOn {β : Type*} {L : Law.MagmaLaw β} (h13 : Equation13 G)
    (hL : @satisfies _ G (t.magma M) L) : L.StructuralOnMagma M :=
  ⟨t.magma M, hL, t.definable_graph M, definable_graph_rev M h13⟩

end Unary13
