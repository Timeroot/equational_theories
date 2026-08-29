import equational_theories.Definability.CaseSplit

/-!
# Source 4274: the eleven types of a pair

Equation `4274` is `x ◇ (x ◇ x) = y ◇ (x ◇ z)`. Its right-hand side does not mention `y`, so every
product `a ◇ (b ◇ c)` is one and the same element `k`; and `k` is itself a product, so writing
`T := im ◇` and `S := G ∖ T` a model of `4274` is exactly the data

* a set `G`, a subset `T ∋ k`, and a map `h : G × S → T` with `{k} ∪ im h = T`,
* the operation `x ◇ y = k` for `y ∈ T` and `x ◇ y = h x y` for `y ∈ S`.

`T`, `k`, `S` and `h` are all `∅`-definable in `M`, so a pair `(x, y)` has one of **eleven** types --
each of `x` and `y` is `k`, in `T ∖ {k}` or in `S`, plus the diagonal cases -- and an operation may
be defined by cases on the type, returning any of the seven definable values `k`, `x`, `y`, `x ◇ y`,
`y ◇ x`, `x ◇ x`, `y ◇ y`. That is a space of about two hundred thousand operations; a scan over
every model on at most five points picks out the six below, which between them settle 98 of the 371
targets `4274` had open.

The forward half of `StructuralOnMagma` is generic: `EOp` extends the decision trees of
`Definability/CaseSplit.lean` with the one test those trees cannot express, membership in `im ◇`,
and `EOp.definable_graph` still hands the graph over for free.

The reverse half is the interesting one, and it is where the six operations were chosen from the
much larger pool of ones that merely satisfy something. Reading `M` back off `M'` means naming `k`,
then `T`, then each entry of `h`:

* `k` is the unique `z` with `z □ z = z`. Every operation below sends the whole diagonal into `T`,
  and `x □ x = x` forces `x ∈ T`; on `T` the diagonal is constantly `k`.
* `T` is `im □`, or -- when the operation puts something outside `T` in the column of `k` -- the
  image of `□` off that column, `{a □ b : b □ b ≠ b}`.
* `h x y` for `y ∈ S` is `x □ y`, except that four of the six move the diagonal of `h` elsewhere:
  `h x x` is then read off `x □ c` for any `c ∈ T ∖ {k}`, with `h x x = k` when there is no such `c`.

## Main results

* `Quad4274.EOp.definable_graph`: the forward half, for any tree with image tests.
* `Quad4274.kernel`: the structure of a model of `4274`.
* `Quad4274.definable_graph_self`, `Quad4274.definable_graph_tcol`,
  `Quad4274.definable_graph_tcolNK`: the three reverse formulas.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

universe u

variable {G : Type}

namespace Quad4274

/-- The `MagmaLanguage` structure of the ambient magma, as an instance. -/
local instance instFOStructure [M : Magma G] : MagmaLanguage.Structure G := M.FOStructure

/-- `a ◇ b`, as a term of the magma language. -/
def ap (G : Type) {α : Type} (a b : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    (MagmaLanguage[[(∅ : Set G)]]).Term α :=
  Functions.apply₂ (L := MagmaLanguage[[(∅ : Set G)]]) (Sum.inl ()) a b

@[simp] theorem realize_ap [Magma G] {α : Type} (v : α → G)
    (a b : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    Term.realize v (ap G a b) = Magma.op (Term.realize v a) (Term.realize v b) := rfl

/-! ### Trees with an image test -/

/-- `∃ p q, p ◇ q = a`: the word `a` lies in the image of the operation. -/
def memFormula (G : Type) (a : FreeMagma (Fin 2)) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex
    (Term.bdEqual (ap G (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))
      ((a.toTerm₂ G).relabel Sum.inl)))

@[simp] theorem realize_memFormula [M : Magma G] (a : FreeMagma (Fin 2))
    (v : Option (Fin 2) → G) :
    (memFormula G a).Realize v ↔ ∃ p q : G, M.op p q = a ⬝ (v ∘ some) := by
  simp only [memFormula, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_bdEqual, realize_ap, Term.realize_var, Term.realize_relabel,
    Sum.elim_comp_inl, FreeMagma.realize_toTerm₂]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨_, _, h⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using h⟩

/-- A test in a decision tree: an equation between words, or membership in the image. -/
inductive Tst : Type
  | eq (a b : FreeMagma (Fin 2)) : Tst
  | mem (a : FreeMagma (Fin 2)) : Tst

/-- A binary operation described as a decision tree whose tests are `Tst`s. -/
inductive EOp : Type
  | leaf (t : FreeMagma (Fin 2)) : EOp
  | ite (c : Tst) (pos neg : EOp) : EOp

/-- What a test says on an assignment. -/
def Tst.holds [M : Magma G] : Tst → (Fin 2 → G) → Prop
  | .eq a b, σ => a ⬝ σ = b ⬝ σ
  | .mem a, σ => ∃ p q : G, M.op p q = a ⬝ σ

/-- The test as a formula in the argument variables `some 0`, `some 1`. -/
def Tst.toFormula (G : Type) : Tst → (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))
  | .eq a b => Term.equal (a.toTerm₂ G) (b.toTerm₂ G)
  | .mem a => memFormula G a

theorem Tst.realize_toFormula [Magma G] (c : Tst) (v : Option (Fin 2) → G) :
    (c.toFormula G).Realize v ↔ c.holds (v ∘ some) := by
  cases c with
  | eq a b => simp [Tst.toFormula, Tst.holds, Formula.realize_equal]
  | mem a => simp [Tst.toFormula, Tst.holds]

open scoped Classical in
/-- The operation the tree describes. -/
noncomputable def EOp.eval [Magma G] : EOp → (Fin 2 → G) → G
  | .leaf t, σ => t ⬝ σ
  | .ite c p n, σ => if c.holds σ then p.eval σ else n.eval σ

/-- The tree as a formula, in the output variable `none` and the arguments `some 0`, `some 1`. -/
def EOp.toFormula (G : Type) :
    EOp → (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))
  | .leaf t => Term.equal (var none) (t.toTerm₂ G)
  | .ite c p n => (c.toFormula G ⊓ p.toFormula G) ⊔ (∼(c.toFormula G) ⊓ n.toFormula G)

theorem EOp.realize_toFormula [Magma G] (q : EOp) (v : Option (Fin 2) → G) :
    (q.toFormula G).Realize v ↔ v none = q.eval (v ∘ some) := by
  classical
  induction q with
  | leaf t => simp [toFormula, eval, Formula.realize_equal]
  | ite c p n ihp ihn =>
    simp only [toFormula, eval, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
      Tst.realize_toFormula, ihp, ihn]
    by_cases h : c.holds (v ∘ some) <;> simp [h]

/-- The magma the tree describes. -/
@[implicit_reducible]
noncomputable def EOp.magma (M : Magma G) (q : EOp) : Magma G :=
  ⟨fun x y ↦ @EOp.eval _ M q ![x, y]⟩

/-- **The forward half.** A decision tree over word equations and image tests has a definable
graph: it is a boolean combination of formulas of the magma language. -/
theorem EOp.definable_graph (M : Magma G) (q : EOp) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ (q.magma M).Graph := by
  refine ⟨q.toFormula G, Set.ext fun v ↦ ?_⟩
  have hv : ![(v ∘ some) 0, (v ∘ some) 1] = (v ∘ some) := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  show @EOp.eval _ M q ![(v ∘ some) 0, (v ∘ some) 1] = v none ↔ _
  rw [hv]
  exact eq_comm.trans (@EOp.realize_toFormula _ M q v).symm

/-! ### The structure of a model of `4274` -/

section Kernel

variable (M : Magma G)

/-- Every product of a product is one and the same element: the law makes `y ◇ (x ◇ z)` independent
of `y` and `z`, and then of `x` as well, because `b ◇ (b ◇ b)` is fixed by every left translation
and is itself a value of `e ◇ ·`. -/
theorem kconst (h : ∀ x y z : G, M.op x (M.op x x) = M.op y (M.op x z)) (b e : G) :
    M.op b (M.op b b) = M.op e (M.op e e) := by
  have h1 := h b e b
  have h2 := h e e (M.op b b)
  have h3 := h b e (M.op b b)
  grind

/-- The data a model of `4274` amounts to: the constant `k`, the image `t`, and the two facts that
say `x ◇ y` is `k` as soon as `y` is a product. -/
structure Ker (M : Magma G) where
  /-- the constant value of every product of a product -/
  k : G
  /-- the image of the operation -/
  t : G → Prop
  /-- every product of a product is `k` -/
  kw : ∀ u : G, M.op u (M.op u u) = k
  /-- `k` is a product -/
  tk : t k
  /-- every product is in the image -/
  tim : ∀ a b : G, t (M.op a b)
  /-- and conversely -/
  tex : ∀ y : G, t y → ∃ a b : G, M.op a b = y
  /-- the whole image is absorbed to `k` on the right -/
  hin : ∀ a b : G, t b → M.op a b = k

/-- Reading the kernel off the law, at any point of the carrier. -/
def kernel (h : ∀ x y z : G, M.op x (M.op x x) = M.op y (M.op x z)) (x₀ : G) : Ker M where
  k := M.op x₀ (M.op x₀ x₀)
  t y := ∃ a b : G, M.op a b = y
  kw u := kconst M h u x₀
  tk := ⟨x₀, M.op x₀ x₀, rfl⟩
  tim a b := ⟨a, b, rfl⟩
  tex _ hy := hy
  hin a b := by
    rintro ⟨p, q, rfl⟩
    rw [← h p a q]
    exact kconst M h p x₀

end Kernel

/-! ### The three reverse formulas -/

section Reverse

/-- the output slot -/
private def z0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl none)
/-- the first argument -/
private def x0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl (some 0))
/-- the second argument -/
private def y0 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0) :=
  Term.var (Sum.inl (some 1))
/-- the output slot, two binders in -/
private def z2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  Term.var (Sum.inl none)
/-- the first argument, two binders in -/
private def x2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  Term.var (Sum.inl (some 0))
/-- the second argument, two binders in -/
private def y2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  Term.var (Sum.inl (some 1))
/-- the outer binder -/
private def a2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  Term.var (Sum.inr 0)
/-- the inner binder -/
private def b2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  Term.var (Sum.inr 1)

/-- `a ◇ b`, the element the two binders name. -/
private def c2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  ap G a2 b2

/-- the outer binder, three binders in -/
private def a3 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 3) :=
  Term.var (Sum.inr 0)
/-- the middle binder -/
private def b3 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 3) :=
  Term.var (Sum.inr 1)
/-- the innermost binder -/
private def e3 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 3) :=
  Term.var (Sum.inr 2)

/-- `a ◇ b` again, one binder further in. -/
private def c3 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 3) :=
  ap G a3 b3

/-- `t` is not a fixed point of the diagonal, i.e. `t ≠ k`. -/
private def nfix {n : ℕ} (t : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin n)) :
    (MagmaLanguage[[(∅ : Set G)]]).BoundedFormula (Option (Fin 2)) n :=
  ∼(Term.bdEqual (ap G t t) t)

/-- `y` is in the image. -/
private def imY : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (Term.bdEqual c2 y2))

/-- `x` is in the image. -/
private def imX : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (Term.bdEqual c2 x2))

/-- `y` is in the image of the columns away from `k`. -/
private def imnkY : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (nfix b2 ⊓ Term.bdEqual c2 y2))

/-- the diagonal read: `z = x □ c` for some `c` in the image with `c ≠ k`, or else `z = k`. -/
private def ddF : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (nfix c2 ⊓ Term.bdEqual z2 (ap G x2 c2))) ⊔
    (∼(BoundedFormula.ex (BoundedFormula.ex (nfix c2))) ⊓ Term.bdEqual (ap G z0 z0) z0)

/-- the diagonal read, off the columns away from `k`. -/
private def ddnkF : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (nfix b2 ⊓ nfix c2 ⊓ Term.bdEqual z2 (ap G x2 c2))) ⊔
    (∼(BoundedFormula.ex (BoundedFormula.ex (nfix b2 ⊓ nfix c2))) ⊓ Term.bdEqual (ap G z0 z0) z0)

/-- `x ◇ y = k` on `T` and `x □ y` off it, for any description `tf` of `T` in the free variable
`y`. Which one is needed depends on the operation: the image is the first thing to try, but an
operation that puts a point of `S` into the table has to be read some other way. -/
def selfFormulaG (G : Type) (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual (ap G z0 z0) z0) ⊔ (∼tf ⊓ Term.bdEqual z0 (ap G x0 y0))

/-- `x ◇ y = k` on the image and `x □ y` off it. -/
def selfFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  selfFormulaG G imY

/-- `x ◇ y = k` on the image, and off it `y □ x` when `x` is in the image and `x □ y` when it is
not: an operation whose rows on `T` carry nothing has to keep `h` in the columns instead. -/
def selfSwapFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (imY ⊓ Term.bdEqual (ap G z0 z0) z0) ⊔
    ((∼imY ⊓ imX) ⊓ Term.bdEqual z0 (ap G y0 x0)) ⊔
    ((∼imY ⊓ ∼imX) ⊓ Term.bdEqual z0 (ap G x0 y0))

/-- the same, with the diagonal of `h` read off a column of the image. -/
def tcolFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (imY ⊓ Term.bdEqual (ap G z0 z0) z0) ⊔
    ((∼imY ⊓ ∼(Term.bdEqual x0 y0)) ⊓ Term.bdEqual z0 (ap G x0 y0)) ⊔
    ((∼imY ⊓ Term.bdEqual x0 y0) ⊓ ddF)

/-- the same again, reading the image off the columns away from `k`. -/
def tcolNKFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (imnkY ⊓ Term.bdEqual (ap G z0 z0) z0) ⊔
    ((∼imnkY ⊓ ∼(Term.bdEqual x0 y0)) ⊓ Term.bdEqual z0 (ap G x0 y0)) ⊔
    ((∼imnkY ⊓ Term.bdEqual x0 y0) ⊓ ddnkF)

/-- the output slot, one binder in -/
private def z1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl none)
/-- the first argument, one binder in -/
private def x1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl (some 0))
/-- the second argument, one binder in -/
private def y1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl (some 1))
/-- the binder -/
private def d1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inr 0)

/-- `z` is a moved value of the diagonal: `d □ d = z` for some `d` with `d □ d ≠ d`. -/
private def iskZ : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G d1 d1) z1 ⊓ ∼(Term.bdEqual (ap G d1 d1) d1))

/-- the diagonal read off the column of `k`: `z = x □ (d □ d)` for a `d` the diagonal moves. -/
private def ddkF : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (∼(Term.bdEqual (ap G d1 d1) d1) ⊓ Term.bdEqual z1 (ap G x1 (ap G d1 d1)))

/-- `y` is fixed by some left translation of `□`. -/
def colanyY (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G d1 y1) y1)

/-- `y` fixes the fixed point of the diagonal of `□`. -/
def kcol0Y (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G d1 d1) d1 ⊓ Term.bdEqual (ap G y1 d1) d1)

/-- `x ◇ y` is `k` on the image, `x □ y` off it, and `x □ k` on the diagonal off the image, with
`k` named as the value the diagonal of `□` moves things to. -/
def kcolMoveFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (imY ⊓ iskZ) ⊔
    ((∼imY ⊓ ∼(Term.bdEqual x0 y0)) ⊓ Term.bdEqual z0 (ap G x0 y0)) ⊔
    ((∼imY ⊓ Term.bdEqual x0 y0) ⊓ ddkF)

/-- `y` is killed by the fixed point of the diagonal of `□` on the left. -/
def krow0Y (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G d1 d1) d1 ⊓ Term.bdEqual (ap G d1 y1) d1)

/-- the outer binder is in `T ∖ {k}`, read as the zero set of the row of `k`: the inner binder is
the fixed point of the diagonal, it kills the outer one, and the outer one is not it. -/
private def tnk2 : (MagmaLanguage[[(∅ : Set G)]]).BoundedFormula (Option (Fin 2)) 2 :=
  (Term.bdEqual (ap G b2 b2) b2 ⊓ Term.bdEqual (ap G b2 a2) b2) ⊓ nfix a2

/-- the diagonal read off a column of `T ∖ {k}`, with `T` the zero set of the row of `k`. -/
private def ddtF : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (tnk2 ⊓ Term.bdEqual z2 (ap G x2 a2))) ⊔
    (∼(BoundedFormula.ex (BoundedFormula.ex tnk2)) ⊓ Term.bdEqual (ap G z0 z0) z0)

/-- `z` is a right zero of `□`. This is the recipe's name for `k` when the diagonal of `□` says
nothing at all -- it is the identity, say -- so that the fixed point read is no use. -/
def rzZ (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.all (Term.bdEqual (ap G d1 z1) z1)

/-- `x ◇ y = k` on the image and `x □ y` off it, for an operation whose diagonal is no use, so
that `k` has to be named as the right zero rather than as the fixed point. -/
def selfRZFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (imY ⊓ rzZ G) ⊔ (∼imY ⊓ Term.bdEqual z0 (ap G x0 y0))

/-- `y` is a product of two *distinct* points. An operation that keeps the diagonal to itself hides
`T` in the rest of the table, and this is what reads it back. -/
def imoffY (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (∼(Term.bdEqual a2 b2) ⊓ Term.bdEqual c2 y2))

/-- `y` is a right zero of `□`, the same read as `rzZ` one variable over. -/
def rzY (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.all (Term.bdEqual (ap G d1 y1) y1)

/-- `T` for the right-zero recipe: the image off the diagonal together with `k` itself. Taking `k`
in by hand rather than as a product of two distinct points is what keeps the read honest on a
one-point carrier, where there are no two distinct points. -/
def imoffkY (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  imoffY G ⊔ rzY G

/-- `a ◇ b` is not a right zero, i.e. `a ◇ b ≠ k`. -/
private def nrz2 : (MagmaLanguage[[(∅ : Set G)]]).BoundedFormula (Option (Fin 2)) 2 :=
  BoundedFormula.ex (∼(Term.bdEqual (ap G e3 c3) c3))

/-- the diagonal read for the right-zero recipe: `z = x □ c` for a `c` off the diagonal of the
image that is not a right zero, or else `z` is the right zero. -/
private def ddoF : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex
      (∼(Term.bdEqual a2 b2) ⊓ nrz2 ⊓ Term.bdEqual z2 (ap G x2 c2))) ⊔
    (∼(BoundedFormula.ex (BoundedFormula.ex (∼(Term.bdEqual a2 b2) ⊓ nrz2))) ⊓ rzZ G)

/-- `x ◇ y` for an operation whose `k` is the right zero and whose `T` is the image off the
diagonal, with the diagonal of `h` read off a column of `T ∖ {k}`. -/
def tcolRZFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (imoffkY G ⊓ rzZ G) ⊔
    ((∼(imoffkY G) ⊓ ∼(Term.bdEqual x0 y0)) ⊓ Term.bdEqual z0 (ap G x0 y0)) ⊔
    ((∼(imoffkY G) ⊓ Term.bdEqual x0 y0) ⊓ ddoF)

/-- `x ◇ y` for an operation that hides the row of `k` in the column of `k`: `k` on `T`, `y □ x`
when `x` is `k`, `x □ y` elsewhere off the diagonal, and a column of `T ∖ {k}` on it. -/
def tcolSwapFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (krow0Y G ⊓ Term.bdEqual (ap G z0 z0) z0) ⊔
    ((∼(krow0Y G) ⊓ ∼(Term.bdEqual x0 y0)) ⊓
      ((Term.bdEqual (ap G x0 x0) x0 ⊓ Term.bdEqual z0 (ap G y0 x0)) ⊔
        (∼(Term.bdEqual (ap G x0 x0) x0) ⊓ Term.bdEqual z0 (ap G x0 y0)))) ⊔
    ((∼(krow0Y G) ⊓ Term.bdEqual x0 y0) ⊓ ddtF)

end Reverse

/-! ### What the reverse formulas say -/

private theorem realize_imY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (imY (G := G)) v xs ↔ ∃ p q : G, P.op p q = v (some 1) := by
  simp only [imY, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual,
    c2, y2, a2, b2, realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨_, _, h⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using h⟩

private theorem realize_imX [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (imX (G := G)) v xs ↔ ∃ p q : G, P.op p q = v (some 0) := by
  simp only [imX, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual,
    c2, x2, a2, b2, realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨_, _, h⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using h⟩

private theorem realize_imnkY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (imnkY (G := G)) v xs ↔
      ∃ p q : G, P.op q q ≠ q ∧ P.op p q = v (some 1) := by
  simp only [imnkY, nfix, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, c2, y2, a2, b2, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨_, _, h⟩
  · rintro ⟨p, q, h1, h2⟩; exact ⟨p, q, by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩

private theorem realize_ddF [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (ddF (G := G)) v xs ↔
      (∃ p q : G, P.op (P.op p q) (P.op p q) ≠ P.op p q ∧
        v none = P.op (v (some 0)) (P.op p q)) ∨
      ((¬ ∃ p q : G, P.op (P.op p q) (P.op p q) ≠ P.op p q) ∧ P.op (v none) (v none) = v none) := by
  simp only [ddF, nfix, BoundedFormula.realize_sup, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual,
    c2, z0, z2, x2, a2, b2, realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  refine or_congr (Iff.intro ?_ ?_) (and_congr_left' (not_congr (Iff.intro ?_ ?_)))
  · rintro ⟨p, q, h1, h2⟩; exact ⟨_, _, h1, h2⟩
  · rintro ⟨p, q, h1, h2⟩; exact ⟨p, q, by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩
  · rintro ⟨p, q, h1⟩; exact ⟨_, _, h1⟩
  · rintro ⟨p, q, h1⟩; exact ⟨p, q, by simpa [Fin.snoc] using h1⟩

private theorem realize_ddnkF [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (ddnkF (G := G)) v xs ↔
      (∃ p q : G, P.op q q ≠ q ∧ P.op (P.op p q) (P.op p q) ≠ P.op p q ∧
        v none = P.op (v (some 0)) (P.op p q)) ∨
      ((¬ ∃ p q : G, P.op q q ≠ q ∧ P.op (P.op p q) (P.op p q) ≠ P.op p q) ∧
        P.op (v none) (v none) = v none) := by
  simp only [ddnkF, nfix, BoundedFormula.realize_sup, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual,
    c2, z0, z2, x2, a2, b2, realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  refine or_congr (Iff.intro ?_ ?_) (and_congr_left' (not_congr (Iff.intro ?_ ?_)))
  · rintro ⟨p, q, ⟨h1, h2⟩, h3⟩; exact ⟨_, _, h1, h2, h3⟩
  · rintro ⟨p, q, h1, h2, h3⟩
    exact ⟨p, q, ⟨by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩,
      by simpa [Fin.snoc] using h3⟩
  · rintro ⟨p, q, h1, h2⟩; exact ⟨_, _, h1, h2⟩
  · rintro ⟨p, q, h1, h2⟩; exact ⟨p, q, by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩

private theorem realize_iskZ [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (iskZ (G := G)) v xs ↔
      ∃ d : G, P.op d d = v none ∧ P.op d d ≠ d := by
  simp only [iskZ, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, z1, d1, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨d, h1, h2⟩; exact ⟨_, h1, h2⟩
  · rintro ⟨d, h1, h2⟩; exact ⟨d, by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩

private theorem realize_ddkF [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (ddkF (G := G)) v xs ↔
      ∃ d : G, P.op d d ≠ d ∧ v none = P.op (v (some 0)) (P.op d d) := by
  simp only [ddkF, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, z1, x1, d1, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨d, h1, h2⟩; exact ⟨_, h1, h2⟩
  · rintro ⟨d, h1, h2⟩; exact ⟨d, by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩

private theorem realize_colanyY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (colanyY G) v xs ↔ ∃ c : G, P.op c (v (some 1)) = v (some 1) := by
  simp only [colanyY, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, y1, d1,
    realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨c, h⟩; exact ⟨_, h⟩
  · rintro ⟨c, h⟩; exact ⟨c, by simpa [Fin.snoc] using h⟩

private theorem realize_kcol0Y [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (kcol0Y G) v xs ↔
      ∃ c : G, P.op c c = c ∧ P.op (v (some 1)) c = c := by
  simp only [kcol0Y, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, y1, d1, realize_ap, Term.realize_var, Sum.elim_inl,
    Sum.elim_inr]
  constructor
  · rintro ⟨c, h1, h2⟩; exact ⟨_, h1, h2⟩
  · rintro ⟨c, h1, h2⟩; exact ⟨c, by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩

private theorem realize_krow0Y [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (krow0Y G) v xs ↔
      ∃ c : G, P.op c c = c ∧ P.op c (v (some 1)) = c := by
  simp only [krow0Y, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, y1, d1, realize_ap, Term.realize_var, Sum.elim_inl,
    Sum.elim_inr]
  constructor
  · rintro ⟨c, h1, h2⟩; exact ⟨_, h1, h2⟩
  · rintro ⟨c, h1, h2⟩; exact ⟨c, by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩

private theorem realize_ddtF [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (ddtF (G := G)) v xs ↔
      (∃ c d : G, (P.op d d = d ∧ P.op d c = d) ∧ P.op c c ≠ c ∧
        v none = P.op (v (some 0)) c) ∨
      ((¬ ∃ c d : G, (P.op d d = d ∧ P.op d c = d) ∧ P.op c c ≠ c) ∧
        P.op (v none) (v none) = v none) := by
  simp only [ddtF, tnk2, nfix, BoundedFormula.realize_sup, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual,
    z0, z2, x2, a2, b2, realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  refine or_congr (Iff.intro ?_ ?_) (and_congr_left' (not_congr (Iff.intro ?_ ?_)))
  · rintro ⟨c, d, ⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨_, _, ⟨h1, h2⟩, h3, h4⟩
  · rintro ⟨c, d, ⟨h1, h2⟩, h3, h4⟩
    exact ⟨c, d, ⟨⟨by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩,
      by simpa [Fin.snoc] using h3⟩, by simpa [Fin.snoc] using h4⟩
  · rintro ⟨c, d, ⟨h1, h2⟩, h3⟩; exact ⟨_, _, ⟨h1, h2⟩, h3⟩
  · rintro ⟨c, d, ⟨h1, h2⟩, h3⟩
    exact ⟨c, d, ⟨by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩,
      by simpa [Fin.snoc] using h3⟩

private theorem realize_rzZ [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (rzZ G) v xs ↔ ∀ u : G, P.op u (v none) = v none := by
  simp only [rzZ, BoundedFormula.realize_all, BoundedFormula.realize_bdEqual, z1, d1, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h u ↦ by simpa [Fin.snoc] using h u, fun h u ↦ by simpa [Fin.snoc] using h u⟩

private theorem realize_imoffY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (imoffY G) v xs ↔ ∃ p q : G, p ≠ q ∧ P.op p q = v (some 1) := by
  simp only [imoffY, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, c2, y2, a2, b2, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨_, _, h⟩
  · rintro ⟨p, q, h1, h2⟩; exact ⟨p, q, by simpa [Fin.snoc] using h1, by simpa [Fin.snoc] using h2⟩

private theorem realize_rzY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (rzY G) v xs ↔ ∀ u : G, P.op u (v (some 1)) = v (some 1) := by
  simp only [rzY, BoundedFormula.realize_all, BoundedFormula.realize_bdEqual, y1, d1, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h u ↦ by simpa [Fin.snoc] using h u, fun h u ↦ by simpa [Fin.snoc] using h u⟩

private theorem realize_imoffkY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (imoffkY G) v xs ↔
      (∃ p q : G, p ≠ q ∧ P.op p q = v (some 1)) ∨ ∀ u : G, P.op u (v (some 1)) = v (some 1) := by
  simp only [imoffkY, BoundedFormula.realize_sup, realize_imoffY, realize_rzY]

private theorem realize_ddoF [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (ddoF (G := G)) v xs ↔
      (∃ p q : G, p ≠ q ∧ (∃ u : G, P.op u (P.op p q) ≠ P.op p q) ∧
        v none = P.op (v (some 0)) (P.op p q)) ∨
      ((¬ ∃ p q : G, p ≠ q ∧ ∃ u : G, P.op u (P.op p q) ≠ P.op p q) ∧
        ∀ u : G, P.op u (v none) = v none) := by
  simp only [ddoF, nrz2, rzZ, BoundedFormula.realize_sup, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_ex, BoundedFormula.realize_all,
    BoundedFormula.realize_bdEqual, c2, c3, z1, z2, x2, a2, b2, a3, b3, d1, e3, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  refine or_congr (Iff.intro ?_ ?_)
    (and_congr (not_congr (Iff.intro ?_ ?_)) (Iff.intro ?_ ?_))
  · rintro ⟨p, q, ⟨h1, u, h2⟩, h3⟩; exact ⟨_, _, h1, ⟨_, h2⟩, h3⟩
  · rintro ⟨p, q, h1, ⟨u, h2⟩, h3⟩
    exact ⟨p, q, ⟨by simpa [Fin.snoc] using h1, u, by simpa [Fin.snoc] using h2⟩,
      by simpa [Fin.snoc] using h3⟩
  · rintro ⟨p, q, h1, u, h2⟩; exact ⟨_, _, h1, _, h2⟩
  · rintro ⟨p, q, h1, u, h2⟩
    exact ⟨p, q, by simpa [Fin.snoc] using h1, u, by simpa [Fin.snoc] using h2⟩
  · exact fun h u ↦ by simpa [Fin.snoc] using h u
  · exact fun h u ↦ by simpa [Fin.snoc] using h u

/-! ### The reverse half -/

variable {M P : Magma G} {t : G → Prop} {k : G}

/-- The simplest read: `x ◇ y` is `k` when `y ∈ T`, and `x □ y` otherwise, where `T` is cut out by
whichever formula `tf` the operation admits. -/
theorem definable_graph_selfG (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hk : ∀ z : G, P.op z z = z ↔ z = k)
    (hin : ∀ a b : G, t b → M.op a b = k)
    (hout : ∀ x y : G, ¬ t y → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨selfFormulaG G tf, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [selfFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hk (v none)
    grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy
    grind

/-- The same with `T` the image of `□`. -/
theorem definable_graph_self
    (hk : ∀ z : G, P.op z z = z ↔ z = k)
    (him : ∀ y : G, (∃ a b : G, P.op a b = y) ↔ t y)
    (hin : ∀ a b : G, t b → M.op a b = k)
    (hout : ∀ x y : G, ¬ t y → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph :=
  definable_graph_selfG imY (fun v xs ↦ (realize_imY v xs).trans (him _)) hk hin hout

/-- The same again for an operation whose diagonal says nothing, so that `k` is the right zero. -/
theorem definable_graph_selfRZ
    (hk : ∀ z : G, (∀ u : G, P.op u z = z) ↔ z = k)
    (him : ∀ y : G, (∃ a b : G, P.op a b = y) ↔ t y)
    (hin : ∀ a b : G, t b → M.op a b = k)
    (hout : ∀ x y : G, ¬ t y → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨selfRZFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [selfRZFormula, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, realize_imY, realize_rzZ,
    him (v (some 1))]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hk (v none)
    grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy
    grind

/-- The same read with the rows of `T` swapped for its columns: an operation whose rows on `T` are
all alike has to be read the other way round, `h x y` off `y □ x` when `x` is in the image. -/
theorem definable_graph_selfSwap
    (hk : ∀ z : G, P.op z z = z ↔ z = k)
    (him : ∀ y : G, (∃ a b : G, P.op a b = y) ↔ t y)
    (hin : ∀ a b : G, t b → M.op a b = k)
    (hsw : ∀ x y : G, ¬ t y → t x → P.op y x = M.op x y)
    (hout : ∀ x y : G, ¬ t y → ¬ t x → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨selfSwapFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [selfSwapFormula, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, realize_imY, realize_imX,
    him (v (some 0)), him (v (some 1))]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hk (v none)
    grind
  by_cases hx : t (v (some 0))
  · have h2 := hsw (v (some 0)) (v (some 1)) hy hx
    grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy hx
    grind

set_option maxHeartbeats 2000000 in
/-- The same, with the diagonal of `h` moved off the diagonal of `□`: `h x x` is read off `x □ c`
for any `c` in the image with `c ≠ k`, and is `k` when the image is just `{k}`. -/
theorem definable_graph_tcol
    (hk : ∀ z : G, P.op z z = z ↔ z = k)
    (him : ∀ y : G, (∃ a b : G, P.op a b = y) ↔ t y)
    (hin : ∀ a b : G, t b → M.op a b = k)
    (htim : ∀ a b : G, t (M.op a b))
    (hout : ∀ x y : G, ¬ t y → x ≠ y → P.op x y = M.op x y)
    (hdd : ∀ x c : G, ¬ t x → t c → c ≠ k → P.op x c = M.op x x) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨tcolFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [tcolFormula, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, z0, x0, y0, realize_ap,
    Term.realize_var, Sum.elim_inl, realize_imY, realize_ddF]
  have hPt : ∀ p q : G, t (P.op p q) := fun p q ↦ (him _).mp ⟨p, q, rfl⟩
  by_cases hy : t (v (some 1))
  · have h1 : (∃ p q : G, P.op p q = v (some 1)) := (him _).mpr hy
    have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hk (v none)
    clear hk him hin htim hout hdd hPt hy
    grind
  have h1 : ¬ (∃ p q : G, P.op p q = v (some 1)) := fun h ↦ hy ((him _).mp h)
  by_cases hxy : v (some 0) = v (some 1)
  · have hx : ¬ t (v (some 0)) := by rw [hxy]; exact hy
    have hdiag : M.op (v (some 0)) (v (some 1)) = M.op (v (some 0)) (v (some 0)) := by rw [hxy]
    by_cases hc : ∃ c : G, t c ∧ c ≠ k
    · obtain ⟨c, hc1, hc2⟩ := hc
      obtain ⟨p, q, rfl⟩ := (him c).mpr hc1
      have h2 : P.op (v (some 0)) (P.op p q) = M.op (v (some 0)) (v (some 0)) :=
        hdd _ _ hx hc1 hc2
      have h3 : P.op (P.op p q) (P.op p q) ≠ P.op p q := fun h ↦ hc2 ((hk _).mp h)
      have h4 : ∀ p' q' : G, P.op (P.op p' q') (P.op p' q') ≠ P.op p' q' →
          P.op (v (some 0)) (P.op p' q') = M.op (v (some 0)) (v (some 0)) :=
        fun p' q' h ↦ hdd _ _ hx (hPt p' q') fun he ↦ h ((hk _).mpr he)
      have hDD : (∃ p' q' : G, P.op (P.op p' q') (P.op p' q') ≠ P.op p' q' ∧
          v none = P.op (v (some 0)) (P.op p' q')) ↔
            v none = M.op (v (some 0)) (v (some 0)) :=
        ⟨fun ⟨p', q', hn, he⟩ ↦ he.trans (h4 p' q' hn),
          fun he ↦ ⟨p, q, h3, he.trans h2.symm⟩⟩
      have hND : ∃ p' q' : G, P.op (P.op p' q') (P.op p' q') ≠ P.op p' q' := ⟨p, q, h3⟩
      clear hk him hin htim hout hdd hPt hy hx hc1 hc2 h2 h3 h4
      grind
    · push Not at hc
      have h2 : ∀ p q : G, P.op p q = k := fun p q ↦ hc _ (hPt p q)
      have h3 : M.op (v (some 0)) (v (some 0)) = k := hc _ (htim _ _)
      have h4 := hk (v none)
      have h5 := hk k
      grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy hxy
    grind

set_option maxHeartbeats 2000000 in
/-- The same read again for an operation that keeps its diagonal free: `k` is not the fixed point of
the diagonal but the right zero, and `T` is not the image but the image off the diagonal. -/
theorem definable_graph_tcolRZ
    (hk : ∀ z : G, (∀ u : G, P.op u z = z) ↔ z = k)
    (him : ∀ y : G, ((∃ a b : G, a ≠ b ∧ P.op a b = y) ∨ ∀ u : G, P.op u y = y) ↔ t y)
    (hin : ∀ a b : G, t b → M.op a b = k)
    (htim : ∀ a b : G, t (M.op a b))
    (hout : ∀ x y : G, ¬ t y → x ≠ y → P.op x y = M.op x y)
    (hdd : ∀ x c : G, ¬ t x → t c → c ≠ k → P.op x c = M.op x x) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  classical
  refine ⟨tcolRZFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [tcolRZFormula, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, realize_imoffkY, realize_rzZ,
    realize_ddoF]
  have hPt : ∀ p q : G, p ≠ q → t (P.op p q) := fun p q h ↦ (him _).mp (Or.inl ⟨p, q, h, rfl⟩)
  by_cases hy : t (v (some 1))
  · have h1 := (him _).mpr hy
    have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hk (v none)
    clear hk him hin htim hout hdd hPt hy
    grind
  have h1 : ¬ ((∃ p q : G, p ≠ q ∧ P.op p q = v (some 1)) ∨
      ∀ u : G, P.op u (v (some 1)) = v (some 1)) := fun h ↦ hy ((him _).mp h)
  by_cases hxy : v (some 0) = v (some 1)
  · have hx : ¬ t (v (some 0)) := by rw [hxy]; exact hy
    have hdiag : M.op (v (some 0)) (v (some 1)) = M.op (v (some 0)) (v (some 0)) := by rw [hxy]
    by_cases hc : ∃ c : G, t c ∧ c ≠ k
    · obtain ⟨c, hc1, hc2⟩ := hc
      obtain ⟨p, q, hpq, rfl⟩ : ∃ a b : G, a ≠ b ∧ P.op a b = c :=
        ((him c).mpr hc1).resolve_right fun h ↦ hc2 ((hk c).mp h)
      have h2 : P.op (v (some 0)) (P.op p q) = M.op (v (some 0)) (v (some 0)) :=
        hdd _ _ hx hc1 hc2
      have h3 : ∃ u : G, P.op u (P.op p q) ≠ P.op p q := by
        by_contra hu
        exact hc2 ((hk _).mp (by push Not at hu; exact hu))
      have h4 : ∀ p' q' : G, p' ≠ q' → (∃ u : G, P.op u (P.op p' q') ≠ P.op p' q') →
          P.op (v (some 0)) (P.op p' q') = M.op (v (some 0)) (v (some 0)) := by
        rintro p' q' hne ⟨u, hu⟩
        exact hdd _ _ hx (hPt p' q' hne) fun he ↦ hu (by rw [he]; exact (hk k).mpr rfl u)
      have hDD : (∃ p' q' : G, p' ≠ q' ∧ (∃ u : G, P.op u (P.op p' q') ≠ P.op p' q') ∧
          v none = P.op (v (some 0)) (P.op p' q')) ↔
            v none = M.op (v (some 0)) (v (some 0)) :=
        ⟨fun ⟨p', q', hne, hn, he⟩ ↦ he.trans (h4 p' q' hne hn),
          fun he ↦ ⟨p, q, hpq, h3, he.trans h2.symm⟩⟩
      have hND : ∃ p' q' : G, p' ≠ q' ∧ ∃ u : G, P.op u (P.op p' q') ≠ P.op p' q' := ⟨p, q, hpq, h3⟩
      clear hk him hin htim hout hdd hPt hy hx hc1 hc2 h2 h3 h4
      grind
    · push Not at hc
      have h5 : ∀ u : G, P.op u k = k := (hk k).mpr rfl
      have h2 : ∀ p q : G, p ≠ q → P.op p q = k := fun p q h ↦ hc _ (hPt p q h)
      have h3 : M.op (v (some 0)) (v (some 0)) = k := hc _ (htim _ _)
      have h4 := hk (v none)
      clear hk him hin htim hout hdd hPt hy hx hc
      grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy hxy
    grind

set_option maxHeartbeats 2000000 in
/-- The same again, reading the image off the columns away from `k`. -/
theorem definable_graph_tcolNK
    (hk : ∀ z : G, P.op z z = z ↔ z = k)
    (him : ∀ y : G, (∃ a b : G, P.op b b ≠ b ∧ P.op a b = y) ↔ t y)
    (hin : ∀ a b : G, t b → M.op a b = k)
    (htim : ∀ a b : G, t (M.op a b))
    (hout : ∀ x y : G, ¬ t y → x ≠ y → P.op x y = M.op x y)
    (hdd : ∀ x c : G, ¬ t x → t c → c ≠ k → P.op x c = M.op x x) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨tcolNKFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [tcolNKFormula, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, realize_imnkY, realize_ddnkF]
  have hPt : ∀ p q : G, P.op q q ≠ q → t (P.op p q) := fun p q h ↦ (him _).mp ⟨p, q, h, rfl⟩
  by_cases hy : t (v (some 1))
  · have h1 : (∃ p q : G, P.op q q ≠ q ∧ P.op p q = v (some 1)) := (him _).mpr hy
    have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hk (v none)
    clear hk him hin htim hout hdd hPt hy
    grind
  have h1 : ¬ (∃ p q : G, P.op q q ≠ q ∧ P.op p q = v (some 1)) := fun h ↦ hy ((him _).mp h)
  by_cases hxy : v (some 0) = v (some 1)
  · have hx : ¬ t (v (some 0)) := by rw [hxy]; exact hy
    have hdiag : M.op (v (some 0)) (v (some 1)) = M.op (v (some 0)) (v (some 0)) := by rw [hxy]
    by_cases hc : ∃ c : G, t c ∧ c ≠ k
    · obtain ⟨c, hc1, hc2⟩ := hc
      obtain ⟨p, q, hq, rfl⟩ := (him c).mpr hc1
      have h2 : P.op (v (some 0)) (P.op p q) = M.op (v (some 0)) (v (some 0)) :=
        hdd _ _ hx hc1 hc2
      have h3 : P.op (P.op p q) (P.op p q) ≠ P.op p q := fun h ↦ hc2 ((hk _).mp h)
      have h4 : ∀ p' q' : G, P.op q' q' ≠ q' → P.op (P.op p' q') (P.op p' q') ≠ P.op p' q' →
          P.op (v (some 0)) (P.op p' q') = M.op (v (some 0)) (v (some 0)) :=
        fun p' q' hq' h ↦ hdd _ _ hx (hPt p' q' hq') fun he ↦ h ((hk _).mpr he)
      have hDD : (∃ p' q' : G, P.op q' q' ≠ q' ∧
          P.op (P.op p' q') (P.op p' q') ≠ P.op p' q' ∧
          v none = P.op (v (some 0)) (P.op p' q')) ↔
            v none = M.op (v (some 0)) (v (some 0)) :=
        ⟨fun ⟨p', q', hq', hn, he⟩ ↦ he.trans (h4 p' q' hq' hn),
          fun he ↦ ⟨p, q, hq, h3, he.trans h2.symm⟩⟩
      have hND : ∃ p' q' : G, P.op q' q' ≠ q' ∧
          P.op (P.op p' q') (P.op p' q') ≠ P.op p' q' := ⟨p, q, hq, h3⟩
      clear hk him hin htim hout hdd hPt hy hx hq hc1 hc2 h2 h3 h4
      grind
    · push Not at hc
      have h2 : ∀ p q : G, P.op q q ≠ q → P.op p q = k := fun p q h ↦ hc _ (hPt p q h)
      have h3 : M.op (v (some 0)) (v (some 0)) = k := hc _ (htim _ _)
      have h4 := hk (v none)
      have h5 := hk k
      have hND : ¬ ∃ p' q' : G, P.op q' q' ≠ q' ∧
          P.op (P.op p' q') (P.op p' q') ≠ P.op p' q' := by
        rintro ⟨p', q', hq', hn⟩
        rw [h2 p' q' hq'] at hn
        exact hn (h5.mpr rfl)
      clear hk him hin htim hout hdd hPt hy hx hc h2
      grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy hxy
    grind

/-- The fourth read. Here the diagonal of `□` is not constant -- it is the identity on `T` -- so `k`
cannot be named as its unique fixed point; it is named instead as the one value the diagonal moves
things to, which needs a point outside `T` to exist at all. The diagonal of `h` is read off the
column of `k`. -/
theorem definable_graph_kcolMove
    (hk : ∀ z : G, (∃ d : G, P.op d d = z ∧ P.op d d ≠ d) ↔ z = k)
    (him : ∀ y : G, (∃ a b : G, P.op a b = y) ↔ t y)
    (hin : ∀ a b : G, t b → M.op a b = k)
    (hout : ∀ x y : G, ¬ t y → x ≠ y → P.op x y = M.op x y)
    (hdd : ∀ x : G, ¬ t x → P.op x k = M.op x x) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨kcolMoveFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [kcolMoveFormula, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, realize_imY, realize_iskZ,
    realize_ddkF]
  by_cases hy : t (v (some 1))
  · have h1 : (∃ p q : G, P.op p q = v (some 1)) := (him _).mpr hy
    have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hk (v none)
    clear hk him hin hout hdd hy
    grind
  have h1 : ¬ (∃ p q : G, P.op p q = v (some 1)) := fun h ↦ hy ((him _).mp h)
  by_cases hxy : v (some 0) = v (some 1)
  · have hx : ¬ t (v (some 0)) := by rw [hxy]; exact hy
    have hdiag : M.op (v (some 0)) (v (some 1)) = M.op (v (some 0)) (v (some 0)) := by rw [hxy]
    have h2 : P.op (v (some 0)) k = M.op (v (some 0)) (v (some 0)) := hdd _ hx
    have h3 : ∀ e : G, P.op e e ≠ e → P.op e e = k := fun e he ↦ (hk _).mp ⟨e, rfl, he⟩
    obtain ⟨d, -, hd⟩ := (hk k).mpr rfl
    clear hk him hin hout hdd hy hx
    grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy hxy
    grind

set_option maxHeartbeats 2000000 in
/-- The fifth read. Here the operation keeps the row of `k` in the column of `k` instead, so the
image of `□` is everything and `T` has to be read as the zero set of the row of `k` -- which is
still a formula in `□` alone, because `k` is the unique fixed point of the diagonal. The diagonal of
`h` is read off a column of `T ∖ {k}`, as in `definable_graph_tcol`. -/
theorem definable_graph_tcolSwap
    (hk : ∀ z : G, P.op z z = z ↔ z = k)
    (hT : ∀ y : G, P.op k y = k ↔ t y)
    (hin : ∀ a b : G, t b → M.op a b = k)
    (htim : ∀ a b : G, t (M.op a b))
    (hout : ∀ x y : G, ¬ t y → x ≠ y → x ≠ k → P.op x y = M.op x y)
    (hsw : ∀ y : G, ¬ t y → P.op y k = M.op k y)
    (hdd : ∀ x c : G, ¬ t x → t c → c ≠ k → P.op x c = M.op x x) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  classical
  refine ⟨tcolSwapFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [tcolSwapFormula, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, realize_krow0Y, realize_ddtF]
  have hkk : P.op k k = k := (hk k).mpr rfl
  have hTt : ∀ y : G, (∃ c : G, P.op c c = c ∧ P.op c y = c) ↔ t y := fun y ↦ by
    refine ⟨fun ⟨c, h1, h2⟩ ↦ (hT y).mp ?_, fun hy ↦ ⟨k, hkk, (hT y).mpr hy⟩⟩
    rwa [(hk c).mp h1] at h2
  by_cases hy : t (v (some 1))
  · have h1 := (hTt (v (some 1))).mpr hy
    have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hk (v none)
    clear hk hT hin htim hout hsw hdd hTt hy
    grind
  have h1 : ¬ (∃ c : G, P.op c c = c ∧ P.op c (v (some 1)) = c) := fun h ↦ hy ((hTt _).mp h)
  by_cases hxy : v (some 0) = v (some 1)
  · have hx : ¬ t (v (some 0)) := by rw [hxy]; exact hy
    have hdiag : M.op (v (some 0)) (v (some 1)) = M.op (v (some 0)) (v (some 0)) := by rw [hxy]
    have hread : ∀ c d : G, P.op d d = d → P.op d c = d → P.op c c ≠ c →
        P.op (v (some 0)) c = M.op (v (some 0)) (v (some 0)) := by
      intro c d hd1 hd2 hc
      rw [(hk d).mp hd1] at hd2
      exact hdd _ _ hx ((hT c).mp hd2) fun he ↦ hc ((hk c).mpr he)
    by_cases hc : ∃ c : G, t c ∧ c ≠ k
    · obtain ⟨c, hc1, hc2⟩ := hc
      have hc3 : P.op c c ≠ c := fun h ↦ hc2 ((hk c).mp h)
      have hDD : (∃ c' d : G, (P.op d d = d ∧ P.op d c' = d) ∧ P.op c' c' ≠ c' ∧
          v none = P.op (v (some 0)) c') ↔ v none = M.op (v (some 0)) (v (some 0)) :=
        ⟨fun ⟨c', d, ⟨hd1, hd2⟩, hc', he⟩ ↦ he.trans (hread c' d hd1 hd2 hc'),
          fun he ↦ ⟨c, k, ⟨hkk, (hT c).mpr hc1⟩, hc3,
            he.trans (hread c k hkk ((hT c).mpr hc1) hc3).symm⟩⟩
      have hND : ∃ c' d : G, (P.op d d = d ∧ P.op d c' = d) ∧ P.op c' c' ≠ c' :=
        ⟨c, k, ⟨hkk, (hT c).mpr hc1⟩, hc3⟩
      clear hk hT hin htim hout hsw hdd hTt hy hx hc1 hc2 hc3 hread
      grind
    · push Not at hc
      have h2 : M.op (v (some 0)) (v (some 0)) = k := hc _ (htim _ _)
      have hND : ¬ ∃ c' d : G, (P.op d d = d ∧ P.op d c' = d) ∧ P.op c' c' ≠ c' := by
        rintro ⟨c', d, ⟨hd1, hd2⟩, hc'⟩
        rw [(hk d).mp hd1] at hd2
        exact hc' ((hk c').mpr (hc c' ((hT c').mp hd2)))
      have h3 := hk (v none)
      clear hk hT hin htim hout hsw hdd hTt hy hx hc hread
      grind
  by_cases hxk : v (some 0) = k
  · have h2 : P.op (v (some 1)) (v (some 0)) = M.op (v (some 0)) (v (some 1)) := by
      rw [hxk]; exact hsw _ hy
    have h3 : P.op (v (some 0)) (v (some 0)) = v (some 0) := (hk _).mpr hxk
    clear hk hT hin htim hout hsw hdd hTt hy
    grind
  · have h2 := hout _ _ hy hxy hxk
    have h3 : ¬ (P.op (v (some 0)) (v (some 0)) = v (some 0)) := fun h ↦ hxk ((hk _).mp h)
    clear hk hT hin htim hout hsw hdd hTt hy
    grind

/-! ### A carrier with at most one point -/

/-- On a subsingleton every law holds and every graph is the whole space, so there is nothing to
prove. This is the one case the six operations below do not cover uniformly: `10986` needs a point
away from `k` to see the image at all. -/
theorem structuralOnMagma_subsingleton [Subsingleton G] {β : Type*} (L : Law.MagmaLaw β)
    (M : Magma G) : L.StructuralOnMagma M := by
  have hd : ∀ N : Magma G,
      @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ N.Graph := fun N ↦
    ⟨Term.bdEqual (Term.var (Sum.inl none)) (Term.var (Sum.inl none)), Set.ext fun v ↦
      ⟨fun _ ↦ rfl, fun _ ↦ show N.op _ _ = _ from Subsingleton.elim _ _⟩⟩
  exact ⟨M, fun _ ↦ Subsingleton.elim _ _, hd M, hd M⟩

/-! ### The six operations

Each is a tree over the five predicates that cut out the eleven types -- `y ∈ T`, `y = k`, `x ∈ T`,
`x = k`, `x = y` -- written in the smallest form that still reads the slot table off. `k` is named
by the word `x ◇ (x ◇ x)`, which is `Ker.kw`. -/

section Ops

open FreeMagma

/-- `x ◇ (x ◇ x)`, the word that names `k`. -/
def kw : FreeMagma (Fin 2) := Lf 0 ⋆ (Lf 0 ⋆ Lf 0)

variable (M : Magma G) (K : Ker M)

/-- The image test of the trees is the kernel's image. -/
private theorem timex (w : G) : (∃ p q : G, M.op p q = w) ↔ K.t w :=
  ⟨fun ⟨p, q, e⟩ ↦ e ▸ K.tim p q, K.tex w⟩

/-! #### Operation `8851`

`k` on the whole of `T` except that `x ◇ x` is copied into the columns of `T ∖ {k}` below `S`, and
the source elsewhere with the diagonal flattened. It settles 36 targets, the most of any. -/

/-- The tree of operation `8851`. -/
def q8851 : EOp :=
  .ite (.mem (Lf 1))
    (.ite (.eq (Lf 1) kw) (.leaf kw)
      (.ite (.mem (Lf 0)) (.leaf kw) (.leaf (Lf 0 ⋆ Lf 0))))
    (.ite (.eq (Lf 0) (Lf 1)) (.leaf kw) (.leaf (Lf 0 ⋆ Lf 1)))

open scoped Classical in
theorem q8851_apply (a b : G) :
    (q8851.magma M).op a b =
      if K.t b then (if b = K.k then K.k else if K.t a then K.k else M.op a a)
      else (if a = b then K.k else M.op a b) := by
  show @EOp.eval _ M q8851 ![a, b] = _
  simp only [q8851, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q8851_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q8851.magma M).FOStructure _ M.Graph := by
  classical
  refine definable_graph_tcol (k := K.k) (t := K.t) ?_ ?_ K.hin K.tim ?_ ?_
  · intro z
    have h1 := K.tk
    have h2 := K.tim z z
    simp only [q8851_apply M K]
    grind
  · intro y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨a, b, rfl⟩
      rw [q8851_apply M K]
      split_ifs <;> first | exact K.tk | exact K.tim _ _
    · by_cases hyk : y = K.k
      · exact ⟨K.k, K.k, by rw [q8851_apply M K, if_pos K.tk, if_pos rfl, hyk]⟩
      · obtain ⟨p, q, rfl⟩ := K.tex y hy
        by_cases hq : K.t q
        · exact absurd (K.hin p q hq) hyk
        · by_cases hpq : p = q
          · subst hpq
            exact ⟨p, M.op p p,
              by rw [q8851_apply M K, if_pos (K.tim p p), if_neg hyk, if_neg hq]⟩
          · exact ⟨p, q, by rw [q8851_apply M K, if_neg hq, if_neg hpq]⟩
  · intro x y hy hxy
    rw [q8851_apply M K, if_neg hy, if_neg hxy]
  · intro x c hx hc hck
    rw [q8851_apply M K, if_pos hc, if_neg hck, if_neg hx]

include K in
/-- The whole of `StructuralOnMagma` for operation `8851`, bar the law itself. -/
theorem structural_q8851 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q8851.magma M) L) : L.StructuralOnMagma M :=
  ⟨q8851.magma M, hL, EOp.definable_graph M q8851, q8851_rev M K⟩

/-! #### Operation `76156`

The plain one: `k` on `T × T`, `x ◇ x` on `S × T`, the source on the columns of `S`. -/

/-- The tree of operation `76156`. -/
def q76156 : EOp :=
  .ite (.mem (Lf 1)) (.ite (.mem (Lf 0)) (.leaf kw) (.leaf (Lf 0 ⋆ Lf 0)))
    (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem q76156_apply (a b : G) :
    (q76156.magma M).op a b =
      if K.t b then (if K.t a then K.k else M.op a a) else M.op a b := by
  show @EOp.eval _ M q76156 ![a, b] = _
  simp only [q76156, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q76156_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q76156.magma M).FOStructure _ M.Graph := by
  classical
  refine definable_graph_self (k := K.k) (t := K.t) ?_ ?_ K.hin ?_
  · intro z
    have h1 := K.tk
    have h2 := K.tim z z
    simp only [q76156_apply M K]
    grind
  · intro y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨a, b, rfl⟩
      rw [q76156_apply M K]
      split_ifs <;> first | exact K.tk | exact K.tim _ _
    · by_cases hyk : y = K.k
      · exact ⟨K.k, K.k, by rw [q76156_apply M K, if_pos K.tk, if_pos K.tk, hyk]⟩
      · obtain ⟨p, q, rfl⟩ := K.tex y hy
        by_cases hq : K.t q
        · exact absurd (K.hin p q hq) hyk
        · exact ⟨p, q, by rw [q76156_apply M K, if_neg hq]⟩
  · intro x y hy
    rw [q76156_apply M K, if_neg hy]

include K in
/-- The whole of `StructuralOnMagma` for operation `76156`, bar the law itself. -/
theorem structural_q76156 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q76156.magma M) L) : L.StructuralOnMagma M :=
  ⟨q76156.magma M, hL, EOp.definable_graph M q76156, q76156_rev M K⟩

/-! #### Operation `76114`

`76156` with `y ◇ x` in place of `x ◇ x`: on `S × T` the source is read off the transpose. -/

/-- The tree of operation `76114`. -/
def q76114 : EOp :=
  .ite (.mem (Lf 1)) (.ite (.mem (Lf 0)) (.leaf kw) (.leaf (Lf 1 ⋆ Lf 0)))
    (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem q76114_apply (a b : G) :
    (q76114.magma M).op a b =
      if K.t b then (if K.t a then K.k else M.op b a) else M.op a b := by
  show @EOp.eval _ M q76114 ![a, b] = _
  simp only [q76114, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q76114_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q76114.magma M).FOStructure _ M.Graph := by
  classical
  refine definable_graph_self (k := K.k) (t := K.t) ?_ ?_ K.hin ?_
  · intro z
    have h1 := K.tk
    have h2 := K.tim z z
    simp only [q76114_apply M K]
    grind
  · intro y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨a, b, rfl⟩
      rw [q76114_apply M K]
      split_ifs <;> first | exact K.tk | exact K.tim _ _
    · by_cases hyk : y = K.k
      · exact ⟨K.k, K.k, by rw [q76114_apply M K, if_pos K.tk, if_pos K.tk, hyk]⟩
      · obtain ⟨p, q, rfl⟩ := K.tex y hy
        by_cases hq : K.t q
        · exact absurd (K.hin p q hq) hyk
        · exact ⟨p, q, by rw [q76114_apply M K, if_neg hq]⟩
  · intro x y hy
    rw [q76114_apply M K, if_neg hy]

include K in
/-- The whole of `StructuralOnMagma` for operation `76114`, bar the law itself. -/
theorem structural_q76114 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q76114.magma M) L) : L.StructuralOnMagma M :=
  ⟨q76114.magma M, hL, EOp.definable_graph M q76114, q76114_rev M K⟩

/-! #### Operation `96337`

The only one whose values on `T × T` are mostly `y`: it is `k` on the diagonal and in the column of
`k` below `S`, `x` in the column of `k` above `T ∖ {k}`, and `y` elsewhere on `T`. -/

/-- The tree of operation `96337`. -/
def q96337 : EOp :=
  .ite (.mem (Lf 1))
    (.ite (.eq (Lf 0) (Lf 1)) (.leaf kw)
      (.ite (.eq (Lf 1) kw) (.ite (.mem (Lf 0)) (.leaf (Lf 0)) (.leaf kw)) (.leaf (Lf 1))))
    (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem q96337_apply (a b : G) :
    (q96337.magma M).op a b =
      if K.t b then (if a = b then K.k else if b = K.k then (if K.t a then a else K.k) else b)
      else M.op a b := by
  show @EOp.eval _ M q96337 ![a, b] = _
  simp only [q96337, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q96337_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q96337.magma M).FOStructure _ M.Graph := by
  classical
  refine definable_graph_self (k := K.k) (t := K.t) ?_ ?_ K.hin ?_
  · intro z
    have h1 := K.tk
    have h2 := K.tim z z
    simp only [q96337_apply M K]
    grind
  · intro y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨a, b, rfl⟩
      rw [q96337_apply M K]
      split_ifs <;> first | exact K.tk | exact K.tim _ _ | assumption
    · by_cases hyk : y = K.k
      · exact ⟨K.k, K.k, by rw [q96337_apply M K, if_pos K.tk, if_pos rfl, hyk]⟩
      · exact ⟨K.k, y, by
          rw [q96337_apply M K, if_pos hy, if_neg (fun e ↦ hyk e.symm), if_neg hyk]⟩
  · intro x y hy
    rw [q96337_apply M K, if_neg hy]

include K in
/-- The whole of `StructuralOnMagma` for operation `96337`, bar the law itself. -/
theorem structural_q96337 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q96337.magma M) L) : L.StructuralOnMagma M :=
  ⟨q96337.magma M, hL, EOp.definable_graph M q96337, q96337_rev M K⟩

/-! #### Operation `27821`

The richest of the six: `x` and `y ◇ x` in the column of `k`, `y` in the row of `k`, `x ◇ x` on
`S × (T ∖ {k})`. -/

/-- The tree of operation `27821`. -/
def q27821 : EOp :=
  .ite (.eq (Lf 0) (Lf 1)) (.leaf kw)
    (.ite (.mem (Lf 1))
      (.ite (.eq (Lf 1) kw)
        (.ite (.mem (Lf 0)) (.leaf (Lf 0)) (.leaf (Lf 1 ⋆ Lf 0)))
        (.ite (.mem (Lf 0)) (.ite (.eq (Lf 0) kw) (.leaf (Lf 1)) (.leaf kw))
          (.leaf (Lf 0 ⋆ Lf 0))))
      (.leaf (Lf 0 ⋆ Lf 1)))

open scoped Classical in
theorem q27821_apply (a b : G) :
    (q27821.magma M).op a b =
      if a = b then K.k
      else if K.t b then
        (if b = K.k then (if K.t a then a else M.op b a)
          else if K.t a then (if a = K.k then b else K.k) else M.op a a)
      else M.op a b := by
  show @EOp.eval _ M q27821 ![a, b] = _
  simp only [q27821, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q27821_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q27821.magma M).FOStructure _ M.Graph := by
  classical
  refine definable_graph_tcol (k := K.k) (t := K.t) ?_ ?_ K.hin K.tim ?_ ?_
  · intro z
    have h1 := K.tk
    simp only [q27821_apply M K]
    exact eq_comm
  · intro y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨a, b, rfl⟩
      rw [q27821_apply M K]
      split_ifs <;> first | exact K.tk | exact K.tim _ _ | assumption
    · by_cases hyk : y = K.k
      · exact ⟨K.k, K.k, by rw [q27821_apply M K, if_pos rfl, hyk]⟩
      · obtain ⟨p, q, rfl⟩ := K.tex y hy
        by_cases hq : K.t q
        · exact absurd (K.hin p q hq) hyk
        · by_cases hpq : p = q
          · subst hpq
            refine ⟨p, M.op p p, ?_⟩
            rw [q27821_apply M K, if_neg (fun e ↦ hq (by rw [e]; exact hy)), if_pos hy, if_neg hyk,
              if_neg hq]
          · exact ⟨p, q, by rw [q27821_apply M K, if_neg hpq, if_neg hq]⟩
  · intro x y hy hxy
    rw [q27821_apply M K, if_neg hxy, if_neg hy]
  · intro x c hx hc hck
    rw [q27821_apply M K, if_neg (fun e ↦ hx (by rw [e]; exact hc)), if_pos hc, if_neg hck, if_neg hx]

include K in
/-- The whole of `StructuralOnMagma` for operation `27821`, bar the law itself. -/
theorem structural_q27821 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q27821.magma M) L) : L.StructuralOnMagma M :=
  ⟨q27821.magma M, hL, EOp.definable_graph M q27821, q27821_rev M K⟩

/-! #### Operation `10986`

The one that puts `x` in the column of `k`, so that the image of `□` is no longer `T`: the reverse
formula has to read the image off the columns away from `k`, which is `tcolNKFormula`. That in turn
needs a point other than `k`, whence the `Nontrivial` hypothesis. -/

/-- The tree of operation `10986`. -/
def q10986 : EOp :=
  .ite (.eq (Lf 0) (Lf 1)) (.leaf kw)
    (.ite (.mem (Lf 1))
      (.ite (.eq (Lf 1) kw) (.leaf (Lf 0))
        (.ite (.mem (Lf 0)) (.leaf kw) (.leaf (Lf 0 ⋆ Lf 0))))
      (.leaf (Lf 0 ⋆ Lf 1)))

open scoped Classical in
theorem q10986_apply (a b : G) :
    (q10986.magma M).op a b =
      if a = b then K.k
      else if K.t b then (if b = K.k then a else if K.t a then K.k else M.op a a)
      else M.op a b := by
  show @EOp.eval _ M q10986 ![a, b] = _
  simp only [q10986, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q10986_rev [Nontrivial G] :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q10986.magma M).FOStructure _ M.Graph := by
  classical
  have hdiag : ∀ z : G, (q10986.magma M).op z z = K.k := fun z ↦ by
    rw [q10986_apply M K, if_pos rfl]
  have hne : ∃ e : G, e ≠ K.k := by
    obtain ⟨u, v, huv⟩ := exists_pair_ne G
    by_cases hu : u = K.k
    · exact ⟨v, fun e ↦ huv (hu.trans e.symm)⟩
    · exact ⟨u, hu⟩
  refine definable_graph_tcolNK (k := K.k) (t := K.t) (fun z ↦ ?_) ?_ K.hin K.tim ?_ ?_
  · rw [hdiag z]
    exact eq_comm
  · intro y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨a, b, hb, rfl⟩
      rw [hdiag b] at hb
      rw [q10986_apply M K]
      split_ifs with h1 h2 h3 h4
      · exact K.tk
      · exact absurd h3.symm hb
      · exact K.tk
      · exact K.tim _ _
      · exact K.tim _ _
    · by_cases hyk : y = K.k
      · obtain ⟨e, he⟩ := hne
        exact ⟨e, e, by rw [hdiag e]; exact fun h ↦ he h.symm,
          by rw [q10986_apply M K, if_pos rfl, hyk]⟩
      · obtain ⟨p, q, rfl⟩ := K.tex y hy
        by_cases hq : K.t q
        · exact absurd (K.hin p q hq) hyk
        · have hqk : q ≠ K.k := fun e ↦ hq (by rw [e]; exact K.tk)
          by_cases hpq : p = q
          · subst hpq
            refine ⟨p, M.op p p, ?_, ?_⟩
            · rw [hdiag (M.op p p)]; exact fun h ↦ hyk h.symm
            · rw [q10986_apply M K, if_neg (fun e ↦ hq (by rw [e]; exact hy)), if_pos hy, if_neg hyk,
                if_neg hq]
          · exact ⟨p, q, by rw [hdiag q]; exact fun h ↦ hqk h.symm,
              by rw [q10986_apply M K, if_neg hpq, if_neg hq]⟩
  · intro x y hy hxy
    rw [q10986_apply M K, if_neg hxy, if_neg hy]
  · intro x c hx hc hck
    rw [q10986_apply M K, if_neg (fun e ↦ hx (by rw [e]; exact hc)), if_pos hc, if_neg hck, if_neg hx]

include K in
/-- The whole of `StructuralOnMagma` for operation `10986`, bar the law itself. -/
theorem structural_q10986 [Nontrivial G] {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q10986.magma M) L) : L.StructuralOnMagma M :=
  ⟨q10986.magma M, hL, EOp.definable_graph M q10986, q10986_rev M K⟩

/-! #### Operation `76065`

`k` on `T × T`, `x` on `S × T`, the source on the columns of `S`. Putting `x` into the table means
the image of `□` is all of `G`, so `T` has to be read some other way: it is the set of `y` with
`y □ k = k`, which is `kcol0Y`. -/

/-- The tree of operation `76065`. -/
def q76065 : EOp :=
  .ite (.mem (Lf 1)) (.ite (.mem (Lf 0)) (.leaf kw) (.leaf (Lf 0))) (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem q76065_apply (a b : G) :
    (q76065.magma M).op a b = if K.t b then (if K.t a then K.k else a) else M.op a b := by
  show @EOp.eval _ M q76065 ![a, b] = _
  simp only [q76065, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q76065_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q76065.magma M).FOStructure _ M.Graph := by
  classical
  have hk : ∀ z : G, (q76065.magma M).op z z = z ↔ z = K.k := fun z ↦ by
    have h1 := K.tk
    have h2 := K.tim z z
    simp only [q76065_apply M K]
    grind
  have hcol : ∀ y : G, (q76065.magma M).op y K.k = if K.t y then K.k else y := fun y ↦ by
    rw [q76065_apply M K, if_pos K.tk]
  refine definable_graph_selfG (t := K.t) (k := K.k) (kcol0Y G) (fun v xs ↦ ?_) hk K.hin ?_
  · rw [realize_kcol0Y (P := q76065.magma M)]
    refine ⟨fun ⟨c, hc1, hc2⟩ ↦ ?_, fun hy ↦ ⟨K.k, by rw [hcol, if_pos K.tk], ?_⟩⟩
    · rw [(hk c).mp hc1, hcol] at hc2
      by_contra hy
      rw [if_neg hy] at hc2
      exact hy (by rw [hc2]; exact K.tk)
    · rw [hcol, if_pos hy]
  · intro x y hy
    rw [q76065_apply M K, if_neg hy]

include K in
/-- The whole of `StructuralOnMagma` for operation `76065`, bar the law itself. -/
theorem structural_q76065 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q76065.magma M) L) : L.StructuralOnMagma M :=
  ⟨q76065.magma M, hL, EOp.definable_graph M q76065, q76065_rev M K⟩

/-! #### Operation `94965`

The same idea with `k` swapped for `y` in the row of `k`, so that `T` is the set of points some left
translation fixes, which is `colanyY`. -/

/-- The tree of operation `94965`. -/
def q94965 : EOp :=
  .ite (.mem (Lf 1))
    (.ite (.eq (Lf 1) kw) (.leaf (Lf 0))
      (.ite (.mem (Lf 0)) (.ite (.eq (Lf 0) kw) (.leaf (Lf 1)) (.leaf kw)) (.leaf (Lf 0))))
    (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem q94965_apply (a b : G) :
    (q94965.magma M).op a b =
      if K.t b then (if b = K.k then a else if K.t a then (if a = K.k then b else K.k) else a)
      else M.op a b := by
  show @EOp.eval _ M q94965 ![a, b] = _
  simp only [q94965, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q94965_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q94965.magma M).FOStructure _ M.Graph := by
  classical
  have hk : ∀ z : G, (q94965.magma M).op z z = z ↔ z = K.k := fun z ↦ by
    have h1 := K.tk
    have h2 := K.tim z z
    simp only [q94965_apply M K]
    grind
  refine definable_graph_selfG (t := K.t) (k := K.k) (colanyY G) (fun v xs ↦ ?_) hk K.hin ?_
  · rw [realize_colanyY (P := q94965.magma M)]
    refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun hy ↦ ⟨K.k, ?_⟩⟩
    · by_contra hy
      rw [q94965_apply M K, if_neg hy] at hc
      exact hy (by rw [← hc]; exact K.tim c (v (some 1)))
    · rw [q94965_apply M K, if_pos hy]
      by_cases hb : v (some 1) = K.k
      · rw [if_pos hb, hb]
      · rw [if_neg hb, if_pos K.tk, if_pos rfl]
  · intro x y hy
    rw [q94965_apply M K, if_neg hy]

include K in
/-- The whole of `StructuralOnMagma` for operation `94965`, bar the law itself. -/
theorem structural_q94965 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q94965.magma M) L) : L.StructuralOnMagma M :=
  ⟨q94965.magma M, hL, EOp.definable_graph M q94965, q94965_rev M K⟩

/-! #### Operation `2999985`

The first from the wider device of `defwork/wide4274.py`, which allows depth-two values: every row
of `T` is the same, carrying `(y ◇ y) ◇ y` on the columns of `S`, and `h` lives in the columns
instead, whence `selfSwapFormula`. The index is the wider device's. -/

/-- The tree of operation `2999985`. -/
def q2999985 : EOp :=
  .ite (.mem (Lf 0))
    (.ite (.mem (Lf 1)) (.leaf kw) (.leaf ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)))
    (.ite (.mem (Lf 1)) (.leaf (Lf 1 ⋆ Lf 0)) (.leaf (Lf 0 ⋆ Lf 1)))

open scoped Classical in
theorem q2999985_apply (a b : G) :
    (q2999985.magma M).op a b =
      if K.t a then (if K.t b then K.k else M.op (M.op b b) b)
      else (if K.t b then M.op b a else M.op a b) := by
  show @EOp.eval _ M q2999985 ![a, b] = _
  simp only [q2999985, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q2999985_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q2999985.magma M).FOStructure _ M.Graph := by
  classical
  refine definable_graph_selfSwap (k := K.k) (t := K.t) (fun z ↦ ?_) (fun y ↦ ?_) K.hin ?_ ?_
  · have h1 := K.tk
    have h2 := K.tim z z
    have h3 := K.tim (M.op z z) z
    have h4 := K.hin z (M.op z z)
    simp only [q2999985_apply M K]
    grind
  · refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨a, b, rfl⟩
      rw [q2999985_apply M K]
      split_ifs <;> first | exact K.tk | exact K.tim _ _
    · obtain ⟨p, q, rfl⟩ := K.tex y hy
      by_cases hq : K.t q
      · exact ⟨K.k, K.k, by rw [q2999985_apply M K, if_pos K.tk, if_pos K.tk, K.hin p q hq]⟩
      · by_cases hp : K.t p
        · exact ⟨q, p, by rw [q2999985_apply M K, if_neg hq, if_pos hp]⟩
        · exact ⟨p, q, by rw [q2999985_apply M K, if_neg hp, if_neg hq]⟩
  · intro x y hy hx
    rw [q2999985_apply M K, if_neg hy, if_pos hx]
  · intro x y hy hx
    rw [q2999985_apply M K, if_neg hx, if_neg hy]

include K in
/-- The whole of `StructuralOnMagma` for operation `2999985`, bar the law itself. -/
theorem structural_q2999985 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q2999985.magma M) L) : L.StructuralOnMagma M :=
  ⟨q2999985.magma M, hL, EOp.definable_graph M q2999985, q2999985_rev M K⟩

/-! #### Operation `4721`

The flattest one: `k` on the whole diagonal and on all of `T × T`, so that the image of `□` is
everything and `T` has to be read as the zero set of the row of `k`. It hides the row of `k` in the
column of `k`, which is `tcolSwapFormula`. -/

/-- The tree of operation `4721`. -/
def q4721 : EOp :=
  .ite (.eq (Lf 0) (Lf 1)) (.leaf kw)
    (.ite (.mem (Lf 0))
      (.ite (.mem (Lf 1)) (.leaf kw)
        (.ite (.eq (Lf 0) kw) (.leaf (Lf 1)) (.leaf (Lf 0 ⋆ Lf 1))))
      (.ite (.mem (Lf 1))
        (.ite (.eq (Lf 1) kw) (.leaf (kw ⋆ Lf 0)) (.leaf (Lf 0 ⋆ Lf 0)))
        (.leaf (Lf 0 ⋆ Lf 1))))

open scoped Classical in
theorem q4721_apply (a b : G) :
    (q4721.magma M).op a b =
      if a = b then K.k
      else if K.t a then (if K.t b then K.k else if a = K.k then b else M.op a b)
      else (if K.t b then (if b = K.k then M.op K.k a else M.op a a) else M.op a b) := by
  show @EOp.eval _ M q4721 ![a, b] = _
  simp only [q4721, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q4721_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q4721.magma M).FOStructure _ M.Graph := by
  classical
  have hdiag : ∀ z : G, (q4721.magma M).op z z = K.k := fun z ↦ by
    rw [q4721_apply M K, if_pos rfl]
  have hrow : ∀ y : G, (q4721.magma M).op K.k y = if K.t y then K.k else y := fun y ↦ by
    rw [q4721_apply M K]
    by_cases hy : K.t y
    · by_cases hky : K.k = y
      · rw [if_pos hky, if_pos hy]
      · rw [if_neg hky, if_pos K.tk, if_pos hy, if_pos hy]
    · have hky : ¬ K.k = y := fun e ↦ hy (e ▸ K.tk)
      rw [if_neg hky, if_pos K.tk, if_neg hy, if_pos rfl, if_neg hy]
  refine definable_graph_tcolSwap (k := K.k) (t := K.t) (fun z ↦ ?_) (fun y ↦ ?_) K.hin K.tim
    ?_ ?_ ?_
  · rw [hdiag z]
    exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
  · rw [hrow y]
    refine ⟨fun h ↦ ?_, fun hy ↦ if_pos hy⟩
    by_contra hy
    rw [if_neg hy] at h
    exact hy (h ▸ K.tk)
  · intro x y hy hxy hxk
    rw [q4721_apply M K, if_neg hxy]
    by_cases hx : K.t x
    · rw [if_pos hx, if_neg hy, if_neg hxk]
    · rw [if_neg hx, if_neg hy]
  · intro y hy
    have hyk : ¬ y = K.k := fun e ↦ hy (e ▸ K.tk)
    rw [q4721_apply M K, if_neg hyk, if_neg hy, if_pos K.tk, if_pos rfl]
  · intro x c hx hc hck
    have hxc : ¬ x = c := fun e ↦ hx (e ▸ hc)
    rw [q4721_apply M K, if_neg hxc, if_neg hx, if_pos hc, if_neg hck]

include K in
/-- The whole of `StructuralOnMagma` for operation `4721`, bar the law itself. -/
theorem structural_q4721 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q4721.magma M) L) : L.StructuralOnMagma M :=
  ⟨q4721.magma M, hL, EOp.definable_graph M q4721, q4721_rev M K⟩

/-! #### Operation `112528`

The one that is the identity on `T`, so that the diagonal of `□` has a fixed point at every element
of `T` and `k` has to be named as the value the diagonal *moves* things to. It reads the diagonal of
`h` off the column of `k`, which is `kcolMoveFormula`; both that and the naming of `k` need a point
outside `T`, whence the `Nontrivial` hypothesis. -/

/-- A nontrivial carrier has a point outside the image: if everything is a product then every
product is `k`, so everything is `k`. -/
private theorem exists_not_mem [Nontrivial G] : ∃ w : G, ¬ K.t w := by
  by_contra hc
  push Not at hc
  obtain ⟨u, u', huu⟩ := exists_pair_ne G
  have h : ∀ a : G, a = K.k := fun a ↦ by
    obtain ⟨p, q, rfl⟩ := K.tex a (hc a)
    exact K.hin p q (hc q)
  exact huu ((h u).trans (h u').symm)

/-- The tree of operation `112528`. -/
def q112528 : EOp :=
  .ite (.mem (Lf 1))
    (.ite (.mem (Lf 0)) (.leaf (Lf 0))
      (.ite (.eq (Lf 1) kw) (.leaf (Lf 0 ⋆ Lf 0)) (.leaf kw)))
    (.ite (.eq (Lf 0) (Lf 1)) (.leaf kw) (.leaf (Lf 0 ⋆ Lf 1)))

open scoped Classical in
theorem q112528_apply (a b : G) :
    (q112528.magma M).op a b =
      if K.t b then (if K.t a then a else if b = K.k then M.op a a else K.k)
      else (if a = b then K.k else M.op a b) := by
  show @EOp.eval _ M q112528 ![a, b] = _
  simp only [q112528, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q112528_rev [Nontrivial G] :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q112528.magma M).FOStructure _ M.Graph := by
  classical
  obtain ⟨w, hw⟩ := exists_not_mem M K
  have hdiag : ∀ d : G, (q112528.magma M).op d d = if K.t d then d else K.k := fun d ↦ by
    rw [q112528_apply M K]
    by_cases hd : K.t d <;> simp [hd]
  refine definable_graph_kcolMove (k := K.k) (t := K.t) (fun z ↦ ?_) ?_ K.hin ?_ ?_
  · refine ⟨?_, fun hz ↦ ⟨w, ?_, ?_⟩⟩
    · rintro ⟨d, h1, h2⟩
      rw [hdiag d] at h1 h2
      split_ifs at h1 h2 with hd
      · exact absurd rfl h2
      · exact h1.symm
    · rw [hdiag w, if_neg hw, hz]
    · rw [hdiag w, if_neg hw]
      exact fun e ↦ hw (e ▸ K.tk)
  · intro y
    refine ⟨?_, fun hy ↦ ⟨y, K.k, ?_⟩⟩
    · rintro ⟨a, b, rfl⟩
      rw [q112528_apply M K]
      split_ifs <;> first | exact K.tk | exact K.tim _ _ | assumption
    · rw [q112528_apply M K, if_pos K.tk, if_pos hy]
  · intro x y hy hxy
    rw [q112528_apply M K, if_neg hy, if_neg hxy]
  · intro x hx
    rw [q112528_apply M K, if_pos K.tk, if_neg hx, if_pos rfl]

include K in
/-- The whole of `StructuralOnMagma` for operation `112528`, bar the law itself. -/
theorem structural_q112528 [Nontrivial G] {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q112528.magma M) L) : L.StructuralOnMagma M :=
  ⟨q112528.magma M, hL, EOp.definable_graph M q112528, q112528_rev M K⟩

/-! #### Operation `1115880`

The one that is the identity on the whole diagonal, so neither the fixed point of the diagonal nor
the value it moves things to says anything: `k` has to be named as the right zero, and the image as
the image *off* the diagonal. That is `tcolRZFormula`. It is otherwise the plainest tree there is --
`k` on `T × T`, the source on the columns of `S`, and `x ◇ x` on `S × (T ∖ {k})`. -/

/-- The tree of operation `1115880`. -/
def q1115880 : EOp :=
  .ite (.mem (Lf 1))
    (.ite (.eq (Lf 1) kw) (.leaf kw)
      (.ite (.eq (Lf 0) (Lf 1)) (.leaf (Lf 0))
        (.ite (.mem (Lf 0)) (.leaf kw) (.leaf (Lf 0 ⋆ Lf 0)))))
    (.ite (.eq (Lf 0) (Lf 1)) (.leaf (Lf 0)) (.leaf (Lf 0 ⋆ Lf 1)))

open scoped Classical in
theorem q1115880_apply (a b : G) :
    (q1115880.magma M).op a b =
      if K.t b then
        (if b = K.k then K.k else if a = b then a else if K.t a then K.k else M.op a a)
      else (if a = b then a else M.op a b) := by
  show @EOp.eval _ M q1115880 ![a, b] = _
  simp only [q1115880, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q1115880_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q1115880.magma M).FOStructure _ M.Graph := by
  classical
  have hkz : ∀ u : G, (q1115880.magma M).op u K.k = K.k := fun u ↦ by
    rw [q1115880_apply M K, if_pos K.tk, if_pos rfl]
  have hdd : ∀ x c : G, ¬ K.t x → K.t c → c ≠ K.k →
      (q1115880.magma M).op x c = M.op x x := fun x c hx hc hck ↦ by
    have hxc : ¬ x = c := fun e ↦ hx (e ▸ hc)
    rw [q1115880_apply M K, if_pos hc, if_neg hck, if_neg hxc, if_neg hx]
  refine definable_graph_tcolRZ (k := K.k) (t := K.t) (fun z ↦ ?_) (fun y ↦ ?_) K.hin K.tim
    (fun x y hy hxy ↦ ?_) hdd
  · -- the right zero is unique: `k □ z` is `k` off the diagonal of `T`, and a product off `T`
    refine ⟨fun h ↦ ?_, fun hz ↦ hz ▸ hkz⟩
    have h1 := h K.k
    rw [q1115880_apply M K] at h1
    have h2 := K.tk
    have h3 := K.tim K.k z
    split_ifs at h1 <;> grind
  · refine ⟨?_, fun hy ↦ ?_⟩
    · rintro (⟨a, b, hab, rfl⟩ | h)
      · rw [q1115880_apply M K]
        have h2 := K.tk
        have h3 : ∀ p q : G, K.t (M.op p q) := K.tim
        split_ifs <;> grind
      · have h1 := h K.k
        rw [q1115880_apply M K] at h1
        by_cases hy : K.t y
        · exact hy
        · rw [if_neg hy] at h1
          by_cases hky : K.k = y
          · exact hky ▸ K.tk
          · rw [if_neg hky] at h1
            exact h1 ▸ K.tim K.k y
    · by_cases hyk : y = K.k
      · exact Or.inr (hyk ▸ hkz)
      obtain ⟨p, q, rfl⟩ := K.tex y hy
      have hq : ¬ K.t q := fun h ↦ hyk (K.hin p q h)
      by_cases hpq : p = q
      · subst hpq
        have hp : ¬ p = M.op p p := fun e ↦ hq (e ▸ K.tim p p)
        exact Or.inl ⟨p, M.op p p, hp, hdd p _ hq hy hyk⟩
      · exact Or.inl ⟨p, q, hpq, by rw [q1115880_apply M K, if_neg hq, if_neg hpq]⟩
  · rw [q1115880_apply M K, if_neg hy, if_neg hxy]

include K in
/-- The whole of `StructuralOnMagma` for operation `1115880`, bar the law itself. -/
theorem structural_q1115880 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q1115880.magma M) L) : L.StructuralOnMagma M :=
  ⟨q1115880.magma M, hL, EOp.definable_graph M q1115880, q1115880_rev M K⟩

/-! #### Operation `1623822`

The source itself off `T`, and on the columns of `T ∖ {k}` the column's own name wherever the row
is outside `T` or on the diagonal. Its diagonal is `k` on `S` and the identity on `T ∖ {k}`, so `k`
is the right zero again; but `h` needs no rearranging, which is `selfRZFormula`. -/

/-- The tree of operation `1623822`. -/
def q1623822 : EOp :=
  .ite (.mem (Lf 1))
    (.ite (.eq (Lf 1) kw) (.leaf kw)
      (.ite (.mem (Lf 0))
        (.ite (.eq (Lf 0) (Lf 1)) (.leaf (Lf 0)) (.leaf kw))
        (.leaf (Lf 1))))
    (.leaf (Lf 0 ⋆ Lf 1))

open scoped Classical in
theorem q1623822_apply (a b : G) :
    (q1623822.magma M).op a b =
      if K.t b then
        (if b = K.k then K.k else if K.t a then (if a = b then a else K.k) else b)
      else M.op a b := by
  show @EOp.eval _ M q1623822 ![a, b] = _
  simp only [q1623822, EOp.eval, Tst.holds, kw, evalInMagma, Matrix.cons_val_zero,
    Matrix.cons_val_one, K.kw, timex M K]

include K in
theorem q1623822_rev :
    @Set.Definable _ (∅ : Set G) MagmaLanguage (q1623822.magma M).FOStructure _ M.Graph := by
  classical
  refine definable_graph_selfRZ (k := K.k) (t := K.t) (fun z ↦ ?_) (fun y ↦ ?_) K.hin
    (fun x y hy ↦ by rw [q1623822_apply M K, if_neg hy])
  · refine ⟨fun h ↦ ?_, fun hz u ↦ by rw [hz, q1623822_apply M K, if_pos K.tk, if_pos rfl]⟩
    have h1 := h K.k
    rw [q1623822_apply M K] at h1
    have h2 := K.tk
    have h3 := K.tim K.k z
    split_ifs at h1 <;> grind
  · refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨a, b, rfl⟩
      rw [q1623822_apply M K]
      have h2 := K.tk
      have h3 : ∀ p q : G, K.t (M.op p q) := K.tim
      split_ifs <;> grind
    · by_cases hyk : y = K.k
      · exact ⟨K.k, K.k, by rw [q1623822_apply M K, if_pos K.tk, if_pos rfl, hyk]⟩
      · exact ⟨y, y, by rw [q1623822_apply M K, if_pos hy, if_neg hyk, if_pos hy, if_pos rfl]⟩

include K in
/-- The whole of `StructuralOnMagma` for operation `1623822`, bar the law itself. -/
theorem structural_q1623822 {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q1623822.magma M) L) : L.StructuralOnMagma M :=
  ⟨q1623822.magma M, hL, EOp.definable_graph M q1623822, q1623822_rev M K⟩

end Ops

end Quad4274
