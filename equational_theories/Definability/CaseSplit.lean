import equational_theories.Definability.Basic
import equational_theories.Equations.All

/-!
# Definitions by cases on term equations

Everything positive in this development so far is a *term*: `Definability/IdempotentPower.lean`,
`QuasigroupWitness.lean` and `OrbitWitness.lean` all end in `TermDefinableOnMagma`, and
`Tarski543.lean` builds one formula by hand. But `DefinableOnMagma` asks only for a first-order
graph, and the gap between the two is exactly where the definability board is stuck: of the 1012
open `definable`/finite cells, 648 are already known *not* to be term-definable, so no amount of
term search will close them.

The cheapest thing living in that gap is a **decision tree over equations between terms**:

    x □ y  =  if a(x, y) = b(x, y) then ... else ...

with terms at the leaves. Its graph is a quantifier-free boolean combination of atomic formulas, so
it is definable for free -- that is `QFOp.definable_graph` below -- while as an operation it is
strictly more expressive than a term, since it can branch.

The example that motivates this is `Equation40`, `x ◇ x = y ◇ y`, which says the square map is
constant. Write `c` for that constant. Then `c` is *named* by the term `x ◇ x`, and the predicate
`y = c` is the term equation `y ◇ y = y` (both sides are `c` exactly when `y` is). So on any magma
satisfying `Equation40` we may define

    x □ y := if y ◇ y = y then x else if x = y then x ◇ x else y

which is the operation "return `y`, except that `c` is a two-sided identity and every element
squares to `c`" -- a genuinely non-term operation, and the one that settles four of the five
targets `Equation40` still had open.

The second section needs no hypothesis on the source at all: overwriting the diagonal,

    x □ y := if x = y then x else x ◇ y

makes the operation idempotent for free, which is enough for `Equation167` and `Equation492`.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw

variable {G : Type}

/-- A binary operation described as a decision tree: the tests are equations between words in the
two arguments, and the leaves are words in the two arguments. -/
inductive QFOp : Type
  | leaf (t : FreeMagma (Fin 2)) : QFOp
  | ite (a b : FreeMagma (Fin 2)) (pos neg : QFOp) : QFOp

/-- The `MagmaLanguage` structure of the ambient magma, as an instance so that `Term.realize` and
`Formula.Realize` can be written without a pile of `@`s. -/
local instance instFOStructure [M : Magma G] : MagmaLanguage.Structure G := M.FOStructure

/-- A word in the two arguments, as a term of the magma language over the variables `some 0` and
`some 1`. The output slot of a graph is `none`, so the arguments are shifted out of its way. -/
def FreeMagma.toTerm₂ (G : Type) :
    FreeMagma (Fin 2) → (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2))
  | .Leaf a => var (some a)
  | m₁ ⋆ m₂ => Functions.apply₂ (Sum.inl ()) (m₁.toTerm₂ G) (m₂.toTerm₂ G)

@[simp] theorem FreeMagma.realize_toTerm₂ [Magma G] (v : Option (Fin 2) → G)
    (t : FreeMagma (Fin 2)) : Term.realize v (t.toTerm₂ G) = t ⬝ (v ∘ some) := by
  induction t with
  | Leaf a => rfl
  | Fork m₁ m₂ ih₁ ih₂ =>
    simp only [FreeMagma.toTerm₂, Term.realize_functions_apply₂, Magma.FOStructure_funMap',
      evalInMagma, ih₁, ih₂]
    rfl

namespace QFOp

open scoped Classical in
/-- The operation the tree describes. -/
noncomputable def eval [Magma G] : QFOp → (Fin 2 → G) → G
  | .leaf t, σ => t ⬝ σ
  | .ite a b p n, σ => if a ⬝ σ = b ⬝ σ then p.eval σ else n.eval σ

/-- The tree as a quantifier-free formula, in the output variable `none` and the arguments
`some 0`, `some 1`. -/
def toFormula (G : Type) :
    QFOp → (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))
  | .leaf t => Term.equal (var none) (t.toTerm₂ G)
  | .ite a b p n =>
    (Term.equal (a.toTerm₂ G) (b.toTerm₂ G) ⊓ p.toFormula G) ⊔
      (∼(Term.equal (a.toTerm₂ G) (b.toTerm₂ G)) ⊓ n.toFormula G)

theorem realize_toFormula [Magma G] (q : QFOp) (v : Option (Fin 2) → G) :
    (q.toFormula G).Realize v ↔ v none = q.eval (v ∘ some) := by
  classical
  induction q with
  | leaf t => simp [toFormula, eval, Formula.realize_equal]
  | ite a b p n ihp ihn =>
    simp only [toFormula, eval, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      Formula.realize_equal, FreeMagma.realize_toTerm₂, ihp, ihn]
    by_cases h : a ⬝ (v ∘ some) = b ⬝ (v ∘ some) <;> simp [h]

/-- The magma the tree describes. -/
@[implicit_reducible]
noncomputable def magma (M : Magma G) (q : QFOp) : Magma G :=
  ⟨fun x y ↦ @eval _ M q ![x, y]⟩

/-- **The point of the file.** A decision tree over term equations has a definable graph: it is a
boolean combination of atomic formulas, with no quantifier anywhere. -/
theorem definable_graph (M : Magma G) (q : QFOp) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ (q.magma M).Graph := by
  refine ⟨q.toFormula G, Set.ext fun v ↦ ?_⟩
  have hv : ![(v ∘ some) 0, (v ∘ some) 1] = (v ∘ some) := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  show @eval _ M q ![(v ∘ some) 0, (v ∘ some) 1] = v none ↔ _
  rw [hv]
  exact eq_comm.trans (@realize_toFormula _ M q v).symm

end QFOp

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- Glue: to define `L` from `L'` it is enough to give one decision tree that satisfies `L` on
every magma satisfying `L'`. -/
theorem definableFrom_of_qfOp (q : QFOp)
    (h : ∀ {G : Type} (M : Magma G), satisfies G L' → @satisfies _ G (q.magma M) L) :
    L.DefinableFrom L' :=
  fun M hM ↦ ⟨_, h M hM, q.definable_graph M⟩

end Law.MagmaLaw

/-! ## The idempotent patch

The other cheap tree needs no hypothesis on the source at all:

    x □ y := if x = y then x else x ◇ y

is the source operation with its diagonal overwritten, so `□` is idempotent whatever `◇` was.
Since only the diagonal moves, any law of `◇` whose two sides stay distinct off the diagonal
survives the patch, and the freshly gained idempotence collapses squares in the target. -/

namespace QFOp

open FreeMagma

/-- `x □ y := if x = y then x else x ◇ y`, the source operation made idempotent. -/
def idem : QFOp :=
  .ite (Lf 0) (Lf 1) (.leaf (Lf 0)) (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem idem_apply (M : Magma G) (a b : G) :
    (idem.magma M).op a b = if a = b then a else M.op a b := by
  show @eval _ M idem ![a, b] = _
  simp only [idem, eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem idem_diag (M : Magma G) (a : G) : (idem.magma M).op a a = a := by
  classical
  rw [idem_apply]
  simp

/-- The patch preserves `Equation167`, `x = (y ◇ x) ◇ (x ◇ y)`.

Off the diagonal there is nothing to check unless `y ◇ x` and `x ◇ y` collide, and they cannot:
`Equation167` at `(x, y)` and at `(y, x)` would then give `x` and `y` the same value. -/
theorem idem_167 (M : Magma G) (h : ∀ x y : G, x = M.op (M.op y x) (M.op x y)) (x y : G) :
    (idem.magma M).op ((idem.magma M).op y x) ((idem.magma M).op x y) = x := by
  classical
  simp only [idem_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_neg (Ne.symm hxy), if_neg hxy]
    have hne : M.op y x ≠ M.op x y := by
      intro he
      exact hxy (((h x y).trans (by rw [he])).trans ((h y x).trans (by rw [he])).symm)
    rw [if_neg hne]
    exact (h x y).symm

end QFOp

namespace Law.MagmaLaw

open QFOp

private theorem idem_law167 {G : Type} (M : Magma G) (hM : satisfies G Law167) (x y : G) :
    (idem.magma M).op ((idem.magma M).op y x) ((idem.magma M).op x y) = x :=
  idem_167 M ((@Law167.models_iff G M).mp hM) x y

theorem Equation1482_definableFrom_Equation167 : Law1482.DefinableFrom Law167 := by
  refine definableFrom_of_qfOp idem fun {G} M hM ↦ ?_
  rw [@Law1482.models_iff]
  intro x y
  rw [idem_diag M y]
  exact (idem_law167 M hM x y).symm

theorem Equation1682_definableFrom_Equation167 : Law1682.DefinableFrom Law167 := by
  refine definableFrom_of_qfOp idem fun {G} M hM ↦ ?_
  rw [@Law1682.models_iff]
  intro x y
  rw [idem_diag M x]
  exact (idem_law167 M hM x y).symm

theorem Equation3675_definableFrom_Equation167 : Law3675.DefinableFrom Law167 := by
  refine definableFrom_of_qfOp idem fun {G} M hM ↦ ?_
  rw [@Law3675.models_iff]
  intro x y
  rw [idem_diag M x]
  exact (idem_law167 M hM x y).symm

/-- `Equation492` forces `(x ◇ y) ◇ x = y`, and hence commutativity. -/
private theorem eq492_comm {G : Type} (M : Magma G) (hM : satisfies G Law492) (a b : G) :
    M.op a b = M.op b a := by
  have h := (@Law492.models_iff G M).mp hM
  have L2 : ∀ a b : G, M.op (M.op a b) a = b := by
    intro a b
    have h1 := h b (M.op a b) a
    rw [← h a b a] at h1
    exact h1.symm
  calc M.op a b
      = M.op a (M.op (M.op (M.op b (M.op b a)) b) (M.op b (M.op b a))) := by
        rw [L2 (M.op b (M.op b a)) b]
    _ = M.op a (M.op (M.op b a) (M.op b (M.op b a))) := by rw [L2 b (M.op b a)]
    _ = M.op b a := (h (M.op b a) a b).symm

theorem Equation332_definableFrom_Equation492 : Law332.DefinableFrom Law492 := by
  refine definableFrom_of_qfOp idem fun {G} M hM ↦ ?_
  classical
  rw [@Law332.models_iff]
  intro x y
  rw [idem_diag M x]
  simp only [idem_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_neg hxy, if_neg (Ne.symm hxy)]
    exact eq492_comm M hM x y

end Law.MagmaLaw

/-! ## Selection operations over `Equation40`

`Equation40` says every square is the same element `c`. That makes `c` nameable by the term
`x ◇ x`, and makes the *predicate* `u = c` equivalent to the term equation `u ◇ u = u` -- both
sides are `c` exactly when `u` is. So on a model of `Equation40` every "selection" operation, one
whose value is always `x`, `y` or `c` and is chosen by the equality type of `(x, y, c)`, is
quantifier-free definable. Two of them settle all five of the targets that `Equation40` still had
open. -/

namespace QFOp

open FreeMagma

/-- `x □ y := if y ◇ y = y then x else if x = y then x ◇ x else y`, that is,
`if y = c then x else if x = y then c else y`. -/
def selA : QFOp :=
  .ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 0))
    (.ite (Lf 0) (Lf 1) (.leaf (Lf 0 ⋆ Lf 0)) (.leaf (Lf 1)))

/-- `x □ y := if y ◇ y = y then x else if x ◇ x = x then y else x ◇ x`, that is,
`if y = c then x else if x = c then y else c`. -/
def selB : QFOp :=
  .ite (Lf 1 ⋆ Lf 1) (Lf 1) (.leaf (Lf 0))
    (.ite (Lf 0 ⋆ Lf 0) (Lf 0) (.leaf (Lf 1)) (.leaf (Lf 0 ⋆ Lf 0)))

variable (M : Magma G) {c : G} (hc : ∀ u : G, M.op u u = c)

include hc

open scoped Classical in
theorem selA_apply (a b : G) :
    (selA.magma M).op a b = if b = c then a else if a = b then c else b := by
  show @eval _ M selA ![a, b] = _
  simp only [selA, eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  by_cases h : b = c
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]

open scoped Classical in
theorem selB_apply (a b : G) :
    (selB.magma M).op a b = if b = c then a else if a = c then b else c := by
  show @eval _ M selB ![a, b] = _
  simp only [selB, eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, hc]
  by_cases h : b = c
  · simp [h]
  · by_cases h' : a = c
    · simp [h, h', Ne.symm h]
    · simp [h, h', Ne.symm h, Ne.symm h']

/-- Every square is `c`: `x □ x = c`. -/
theorem selA_sq (a : G) : (selA.magma M).op a a = c := by
  rw [selA_apply M hc]
  by_cases h : a = c <;> simp [h]

/-- `c` is a right identity: `x □ c = x`. -/
theorem selA_rc (a : G) : (selA.magma M).op a c = a := by
  rw [selA_apply M hc]
  simp

/-- The reduced form of `Equation504` and `Equation508`, once the inner square has collapsed. -/
theorem selA_swap (x y : G) : x = (selA.magma M).op y ((selA.magma M).op y x) := by
  by_cases hx : x = c
  · subst hx
    rw [selA_rc M hc, selA_sq M hc]
  · by_cases hxy : y = x <;> simp [selA_apply M hc, hx, hxy]

end QFOp

namespace Law.MagmaLaw

open QFOp

/-- The constant `c` of `Equation40`, as an opaque element: naming it rather than carrying
`x ◇ x` around is what keeps the case analysis below from rewriting in circles. -/
private theorem sel_const {G : Type} (M : Magma G) (hM : satisfies G Law40) (x : G) :
    ∃ c : G, ∀ u : G, M.op u u = c :=
  ⟨M.op x x, fun u ↦ (@Law40.models_iff G M).mp hM u x⟩

theorem Equation504_definableFrom_Equation40 : Law504.DefinableFrom Law40 := by
  refine definableFrom_of_qfOp selA fun {G} M hM ↦ ?_
  rw [@Law504.models_iff]
  intro x y
  obtain ⟨c, hc⟩ := sel_const M hM x
  rw [selA_sq M hc y, selA_rc M hc x]
  exact selA_swap M hc x y

theorem Equation508_definableFrom_Equation40 : Law508.DefinableFrom Law40 := by
  refine definableFrom_of_qfOp selA fun {G} M hM ↦ ?_
  rw [@Law508.models_iff]
  intro x y z
  obtain ⟨c, hc⟩ := sel_const M hM x
  rw [selA_sq M hc z, selA_rc M hc x]
  exact selA_swap M hc x y

theorem Equation1519_definableFrom_Equation40 : Law1519.DefinableFrom Law40 := by
  refine definableFrom_of_qfOp selA fun {G} M hM ↦ ?_
  rw [@Law1519.models_iff]
  intro x y
  obtain ⟨c, hc⟩ := sel_const M hM x
  simp only [selA_apply M hc]
  by_cases hx : x = c <;> by_cases hy : y = c <;> by_cases hxy : x = y <;> simp_all

theorem Equation1523_definableFrom_Equation40 : Law1523.DefinableFrom Law40 := by
  refine definableFrom_of_qfOp selA fun {G} M hM ↦ ?_
  rw [@Law1523.models_iff]
  intro x y z
  obtain ⟨c, hc⟩ := sel_const M hM x
  simp only [selA_apply M hc]
  by_cases hx : x = c <;> by_cases hy : y = c <;> by_cases hxy : x = y <;> simp_all

theorem Equation1479_definableFrom_Equation40 : Law1479.DefinableFrom Law40 := by
  refine definableFrom_of_qfOp selB fun {G} M hM ↦ ?_
  rw [@Law1479.models_iff]
  intro x y
  obtain ⟨c, hc⟩ := sel_const M hM x
  simp only [selB_apply M hc]
  by_cases hx : x = c <;> by_cases hy : y = c <;> by_cases hxy : x = y <;> simp_all

end Law.MagmaLaw
