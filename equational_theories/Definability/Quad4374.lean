import equational_theories.Definability.Quad4274

/-!
# The column-constant family: `k` promoted to a function

Equation `4374` is `x ◇ (y ◇ z) = w ◇ (y ◇ z)`: a product depends only on its right argument as
soon as that argument is itself a product. Writing `T := im ◇` and `S := G ∖ T`, a model is exactly

* a set `G`, a subset `T`, a map `γ : T → T` and a completely free `h : G × S → T`,
* the operation `x ◇ y = γ y` for `y ∈ T` and `x ◇ y = h x y` for `y ∈ S`,

subject only to `γ(T) ∪ im h = T`, which is what makes `T` the image.

This is `Definability/Quad4274.lean` with the constant `k` promoted to a function, and law `4274`
is the case `γ` constant. The promotion costs almost nothing and buys a great deal: thirty-one open
sources of the board imply `4374` up to duality, against `4274`'s one.

The reverse half becomes *easier*, not harder. Naming `k` took a library of a hundred and thirty
descriptions in `Quad4274`, of which only a handful were ever usable; here there is nothing to
name, because `γ y = y ◇ y` is a word. So the reverse read only has to say where the operation
keeps that word, and where it keeps `h`.

## Main results

* `Quad4374.GKer`: the structure of a model of `4374`.
* `Quad4374.gkernel`: reading it off the law.
* `Quad4374.definable_graph_selfGamma`: the reverse formula for an operation that keeps `γ` on the
  diagonal of `T` and the source itself on the columns of `S`.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma Quad4274

universe u

variable {G : Type}

namespace Quad4374

/-- The `MagmaLanguage` structure of the ambient magma, as an instance. -/
local instance instFOStructure [M : Magma G] : MagmaLanguage.Structure G := M.FOStructure

/-! ### The structure of a model of `4374` -/

/-- The data a model of `4374` amounts to: the image `t`, and the one fact that says a product's
left argument is forgotten as soon as its right argument is a product. There is no constant to
carry, because `γ b` is `b ◇ b`. -/
structure GKer (M : Magma G) where
  /-- the image of the operation -/
  t : G → Prop
  /-- every product is in the image -/
  tim : ∀ a b : G, t (M.op a b)
  /-- and conversely -/
  tex : ∀ y : G, t y → ∃ a b : G, M.op a b = y
  /-- on the image the left argument is forgotten, so the value is the right argument's square -/
  hin : ∀ a b : G, t b → M.op a b = M.op b b

/-- Reading the kernel off the law. -/
def gkernel (M : Magma G) (h : ∀ x y z w : G, M.op x (M.op y z) = M.op w (M.op y z)) : GKer M where
  t y := ∃ a b : G, M.op a b = y
  tim a b := ⟨a, b, rfl⟩
  tex _ hy := hy
  hin a b := by
    rintro ⟨p, q, rfl⟩
    exact h a p q (M.op p q)

/-! ### The reverse formulas -/

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
/-- the first argument, one binder in -/
private def x1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl (some 0))
/-- the second argument, one binder in -/
private def y1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inl (some 1))
/-- the only binder -/
private def d1 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 1) :=
  Term.var (Sum.inr 0)
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

/-- `a □ b`, the element the two binders name. -/
private def c2 : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 2) :=
  ap G a2 b2

/-- `y` is in the image. -/
private def imY : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (Term.bdEqual c2 y2))

private theorem realize_imY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (imY (G := G)) v xs ↔ ∃ p q : G, P.op p q = v (some 1) := by
  simp only [imY, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual,
    c2, y2, a2, b2, realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨_, _, h⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using h⟩

/-- `x` is in the image: the same description, read in the first argument. -/
private def imX : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (Term.bdEqual c2 x2))

private theorem realize_imX [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (imX (G := G)) v xs ↔ ∃ p q : G, P.op p q = v (some 0) := by
  simp only [imX, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual,
    c2, x2, a2, b2, realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨_, _, h⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using h⟩

/-- `y` is the product of two *distinct* elements. -/
private def imoffY : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (∼(Term.bdEqual a2 b2) ⊓ Term.bdEqual c2 y2))

private theorem realize_imoffY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (imoffY (G := G)) v xs ↔
      ∃ p q : G, p ≠ q ∧ P.op p q = v (some 1) := by
  simp only [imoffY, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, c2, y2, a2, b2, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, hne, h⟩; exact ⟨_, _, hne, h⟩
  · rintro ⟨p, q, hne, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using hne, by simpa [Fin.snoc] using h⟩

/-- `y` is a product that differs from its own left argument. -/
private def imdiag0Y : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (∼(Term.bdEqual c2 a2) ⊓ Term.bdEqual c2 y2))

private theorem realize_imdiag0Y [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (imdiag0Y (G := G)) v xs ↔
      ∃ p q : G, P.op p q ≠ p ∧ P.op p q = v (some 1) := by
  simp only [imdiag0Y, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, c2, y2, a2, b2, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, hne, h⟩; exact ⟨_, _, hne, h⟩
  · rintro ⟨p, q, hne, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using hne, by simpa [Fin.snoc] using h⟩

/-- `y □ d = y` for some `d`: the second argument absorbs on the left. -/
private def rowanyY : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G y1 d1) y1)

private theorem realize_rowanyY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (rowanyY (G := G)) v xs ↔ ∃ d : G, P.op (v (some 1)) d = v (some 1) := by
  simp only [rowanyY, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, y1, d1,
    realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨d, h⟩; exact ⟨_, h⟩
  · rintro ⟨d, h⟩; exact ⟨d, by simpa [Fin.snoc] using h⟩

/-- `x □ d = x` for some `d`: the same description, read in the first argument. -/
private def rowanyX : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G x1 d1) x1)

private theorem realize_rowanyX [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (rowanyX (G := G)) v xs ↔ ∃ d : G, P.op (v (some 0)) d = v (some 0) := by
  simp only [rowanyX, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, x1, d1,
    realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨d, h⟩; exact ⟨_, h⟩
  · rintro ⟨d, h⟩; exact ⟨d, by simpa [Fin.snoc] using h⟩

/-- `y □ d = d` for some `d`: the second argument fixes something on the right. -/
private def rowfixY : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G y1 d1) d1)

private theorem realize_rowfixY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (rowfixY (G := G)) v xs ↔ ∃ d : G, P.op (v (some 1)) d = d := by
  simp only [rowfixY, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, y1, d1,
    realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨d, h⟩; exact ⟨_, h⟩
  · rintro ⟨d, h⟩; exact ⟨d, by simpa [Fin.snoc] using h⟩

/-- `d □ y = d` for some `d`: the second argument fixes something on the left. -/
private def colfixY : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (Term.bdEqual (ap G d1 y1) d1)

private theorem realize_colfixY [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (colfixY (G := G)) v xs ↔ ∃ d : G, P.op d (v (some 1)) = d := by
  simp only [colfixY, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, y1, d1,
    realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨d, h⟩; exact ⟨_, h⟩
  · rintro ⟨d, h⟩; exact ⟨d, by simpa [Fin.snoc] using h⟩

/-- `z = x □ c` for some `c` that is a product of two distinct elements: how a diagonal cell of `S`
is read back off a *column* of `T`, when `T` is `imoff`. -/
private def tcolOffF : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (∼(Term.bdEqual a2 b2) ⊓ Term.bdEqual z2 (ap G x2 c2)))

private theorem realize_tcolOffF [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (tcolOffF (G := G)) v xs ↔
      ∃ p q : G, p ≠ q ∧ v none = P.op (v (some 0)) (P.op p q) := by
  simp only [tcolOffF, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, c2, z2, x2, a2, b2, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, hne, h⟩; exact ⟨_, _, hne, h⟩
  · rintro ⟨p, q, hne, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using hne, by simpa [Fin.snoc] using h⟩

/-- `z = c □ x` for some product `c` that differs from its left argument: the same read off a *row*
of `T`, when `T` is `imdiag0`. -/
private def trowDiag0F : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (∼(Term.bdEqual c2 a2) ⊓ Term.bdEqual z2 (ap G c2 x2)))

private theorem realize_trowDiag0F [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (trowDiag0F (G := G)) v xs ↔
      ∃ p q : G, P.op p q ≠ p ∧ v none = P.op (P.op p q) (v (some 0)) := by
  simp only [trowDiag0F, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, c2, z2, x2, a2, b2, realize_ap,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, hne, h⟩; exact ⟨_, _, hne, h⟩
  · rintro ⟨p, q, hne, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using hne, by simpa [Fin.snoc] using h⟩

/-- `y □ y` when `y` is in the image, and `x □ y` otherwise: the simplest read there is, and the one
the promotion of `k` to `γ` makes possible at all. -/
def selfGammaFormulaG (G : Type) (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G y0 y0)) ⊔ (∼tf ⊓ Term.bdEqual z0 (ap G x0 y0))

/-- The same with `T` the image of `□`. -/
def selfGammaFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  selfGammaFormulaG G imY

variable {M P : Magma G} {t : G → Prop}

/-- The simplest read: `x ◇ y` is `y □ y` when `y ∈ T`, and `x □ y` otherwise, where `T` is cut out
by whichever formula `tf` the operation admits. -/
theorem definable_graph_selfGammaG
    (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y)
    (hout : ∀ x y : G, ¬ t y → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨selfGammaFormulaG G tf, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [selfGammaFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hg (v (some 1)) hy
    grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy
    grind

/-- The same with `T` the image of `□`. -/
theorem definable_graph_selfGamma
    (him : ∀ y : G, (∃ a b : G, P.op a b = y) ↔ t y)
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y)
    (hout : ∀ x y : G, ¬ t y → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph :=
  definable_graph_selfGammaG imY (fun v xs ↦ (realize_imY (P := P) v xs).trans (him _)) hin hg hout

/-- The same read with the columns of `S` transposed. -/
def swapGammaFormulaG (G : Type) (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G y0 y0)) ⊔ (∼tf ⊓ Term.bdEqual z0 (ap G y0 x0))

/-- `x ◇ y` is `y □ y` when `y ∈ T`, and `y □ x` otherwise. The diagonal needs no separate branch:
at `x = y` the transposed read is the direct one. -/
theorem definable_graph_swapGammaG
    (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y)
    (hout : ∀ x y : G, ¬ t y → P.op y x = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨swapGammaFormulaG G tf, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [swapGammaFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hg (v (some 1)) hy
    grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy
    grind

/-- The read that transposes only where the first argument is in `T`. -/
def splitGammaFormulaG (G : Type)
    (tf xf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G y0 y0))
    ⊔ ((∼tf ⊓ xf) ⊓ Term.bdEqual z0 (ap G y0 x0))
    ⊔ ((∼tf ⊓ ∼xf) ⊓ Term.bdEqual z0 (ap G x0 y0))

/-- `x ◇ y` is `y □ y` on `T`; off it the cell is `y □ x` when `x ∈ T` and `x □ y` when `x ∉ T`.
The diagonal of `S` falls in the last branch, where the read is direct, so again there is no case
for it. -/
theorem definable_graph_splitGammaG
    (tf xf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hxf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize xf v xs ↔ t (v (some 0)))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y)
    (hts : ∀ x y : G, t x → ¬ t y → P.op y x = M.op x y)
    (hss : ∀ x y : G, ¬ t x → ¬ t y → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨splitGammaFormulaG G tf xf, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [splitGammaFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf, hxf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hg (v (some 1)) hy
    grind
  · by_cases hx : t (v (some 0))
    · have h2 := hts (v (some 0)) (v (some 1)) hx hy
      grind
    · have h2 := hss (v (some 0)) (v (some 1)) hx hy
      grind

/-- The read that transposes only where the first argument is *outside* `T`. -/
def splitGammaFormulaG' (G : Type)
    (tf xf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G y0 y0))
    ⊔ ((∼tf ⊓ xf) ⊓ Term.bdEqual z0 (ap G x0 y0))
    ⊔ ((∼tf ⊓ ∼xf) ⊓ Term.bdEqual z0 (ap G y0 x0))

/-- The mirror of `definable_graph_splitGammaG`: `x □ y` when `x ∈ T` and `y □ x` when `x ∉ T`. -/
theorem definable_graph_splitGammaG'
    (tf xf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hxf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize xf v xs ↔ t (v (some 0)))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y)
    (hts : ∀ x y : G, t x → ¬ t y → P.op x y = M.op x y)
    (hss : ∀ x y : G, ¬ t x → ¬ t y → P.op y x = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨splitGammaFormulaG' G tf xf, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [splitGammaFormulaG', Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf, hxf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hg (v (some 1)) hy
    grind
  · by_cases hx : t (v (some 0))
    · have h2 := hts (v (some 0)) (v (some 1)) hx hy
      grind
    · have h2 := hss (v (some 0)) (v (some 1)) hx hy
      grind

/-- The general read whose diagonal branch is a formula of its own: `y □ y` on `T`, the formula
`df` on the diagonal of `S`, and the term `oa` everywhere else. -/
def ddGammaFormulaG (G : Type)
    (tf df : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (oa : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0)) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G y0 y0))
    ⊔ ((∼tf ⊓ Term.bdEqual x0 y0) ⊓ df)
    ⊔ ((∼tf ⊓ ∼(Term.bdEqual x0 y0)) ⊓ Term.bdEqual z0 oa)

theorem definable_graph_ddGammaG
    (tf df : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (oa : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hdf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G), ¬ t (v (some 1)) →
      v (some 0) = v (some 1) →
      (BoundedFormula.Realize df v xs ↔ v none = M.op (v (some 0)) (v (some 1))))
    (hoa : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G), ¬ t (v (some 1)) →
      v (some 0) ≠ v (some 1) →
      Term.realize (Sum.elim v xs) oa = M.op (v (some 0)) (v (some 1)))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨ddGammaFormulaG G tf df oa, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hg (v (some 1)) hy
    simp only [ddGammaFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
      BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
      z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf]
    grind
  · by_cases hxy : v (some 0) = v (some 1)
    · have h4 := hdf v default hy hxy
      simp only [ddGammaFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
        BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
        z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf]
      grind
    · have h5 := hoa v default hy hxy
      simp only [ddGammaFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
        BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
        z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf]
      grind

/-- `T` is the set of products of distinct elements, the diagonal of `S` is read off any column of
`T`, and everything else is read directly. -/
theorem definable_graph_tcolOffGamma
    (him : ∀ y : G, (∃ p q : G, p ≠ q ∧ P.op p q = y) ↔ t y)
    (htim : ∀ a b : G, t (M.op a b))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y)
    (hdd : ∀ x c : G, ¬ t x → t c → P.op x c = M.op x x)
    (hout : ∀ x y : G, ¬ t y → x ≠ y → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine definable_graph_ddGammaG imoffY tcolOffF (ap G x0 y0)
    (fun v xs ↦ (realize_imoffY v xs).trans (him _)) (fun v xs hy hxy ↦ ?_) (fun v xs hy hxy ↦ ?_)
    hin hg
  · have hx : ¬ t (v (some 0)) := hxy ▸ hy
    rw [realize_tcolOffF]
    constructor
    · rintro ⟨p, q, hne, h⟩
      rw [h, hdd _ _ hx ((him _).1 ⟨p, q, hne, rfl⟩), hxy]
    · rintro h
      obtain ⟨p, q, hne, hpq⟩ := (him (M.op (v (some 0)) (v (some 0)))).2 (htim _ _)
      exact ⟨p, q, hne, by rw [h, ← hxy, hdd _ _ hx ((him _).1 ⟨p, q, hne, rfl⟩)]⟩
  · simpa [x0, y0, realize_ap] using hout _ _ hy hxy

/-- `T` is the set of products differing from their left argument, the diagonal of `S` is read off
any row of `T`, and everything else is read transposed. -/
theorem definable_graph_trowDiag0Gamma
    (him : ∀ y : G, (∃ p q : G, P.op p q ≠ p ∧ P.op p q = y) ↔ t y)
    (htim : ∀ a b : G, t (M.op a b))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y)
    (hdd : ∀ x c : G, ¬ t x → t c → P.op c x = M.op x x)
    (hout : ∀ x y : G, ¬ t y → x ≠ y → P.op y x = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine definable_graph_ddGammaG imdiag0Y trowDiag0F (ap G y0 x0)
    (fun v xs ↦ (realize_imdiag0Y v xs).trans (him _)) (fun v xs hy hxy ↦ ?_) (fun v xs hy hxy ↦ ?_)
    hin hg
  · have hx : ¬ t (v (some 0)) := hxy ▸ hy
    rw [realize_trowDiag0F]
    constructor
    · rintro ⟨p, q, hne, h⟩
      rw [h, hdd _ _ hx ((him _).1 ⟨p, q, hne, rfl⟩), hxy]
    · rintro h
      obtain ⟨p, q, hne, hpq⟩ := (him (M.op (v (some 0)) (v (some 0)))).2 (htim _ _)
      exact ⟨p, q, hne, by rw [h, ← hxy, hdd _ _ hx ((him _).1 ⟨p, q, hne, rfl⟩)]⟩
  · simpa [x0, y0, realize_ap] using hout _ _ hy hxy

/-- `z = x □ c` for some product `c`: how a diagonal cell of `S` is read back off a *column* of
`T`, when `T` is the image. -/
private def tcolF : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (Term.bdEqual z2 (ap G x2 c2)))

private theorem realize_tcolF [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (tcolF (G := G)) v xs ↔
      ∃ p q : G, v none = P.op (v (some 0)) (P.op p q) := by
  simp only [tcolF, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, c2, z2, x2, a2, b2,
    realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨_, _, h⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using h⟩

/-- `z = c □ x` for some product `c`: the same read off a *row* of `T`. -/
private def trowF : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  BoundedFormula.ex (BoundedFormula.ex (Term.bdEqual z2 (ap G c2 x2)))

private theorem realize_trowF [P : Magma G] (v : Option (Fin 2) → G) (xs : Fin 0 → G) :
    BoundedFormula.Realize (trowF (G := G)) v xs ↔
      ∃ p q : G, v none = P.op (P.op p q) (v (some 0)) := by
  simp only [trowF, BoundedFormula.realize_ex, BoundedFormula.realize_bdEqual, c2, z2, x2, a2, b2,
    realize_ap, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨p, q, h⟩; exact ⟨_, _, h⟩
  · rintro ⟨p, q, h⟩; exact ⟨p, q, by simpa [Fin.snoc] using h⟩

/-- The widest read of all: `y □ y` on `T`, the formula `df` on the diagonal of `S`, the term `oa`
off it where `x ∈ T`, and the term `ob` off it where `x ∉ T`. -/
def ddSplitFormulaG (G : Type)
    (tf xf df : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (oa ob : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0)) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G y0 y0))
    ⊔ ((∼tf ⊓ Term.bdEqual x0 y0) ⊓ df)
    ⊔ ((∼tf ⊓ ∼(Term.bdEqual x0 y0) ⊓ xf) ⊓ Term.bdEqual z0 oa)
    ⊔ ((∼tf ⊓ ∼(Term.bdEqual x0 y0) ⊓ ∼xf) ⊓ Term.bdEqual z0 ob)

theorem definable_graph_ddSplitG
    (tf xf df : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (oa ob : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hxf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize xf v xs ↔ t (v (some 0)))
    (hdf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G), ¬ t (v (some 1)) →
      v (some 0) = v (some 1) →
      (BoundedFormula.Realize df v xs ↔ v none = M.op (v (some 0)) (v (some 1))))
    (hoa : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G), ¬ t (v (some 1)) →
      v (some 0) ≠ v (some 1) → t (v (some 0)) →
      Term.realize (Sum.elim v xs) oa = M.op (v (some 0)) (v (some 1)))
    (hob : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G), ¬ t (v (some 1)) →
      v (some 0) ≠ v (some 1) → ¬ t (v (some 0)) →
      Term.realize (Sum.elim v xs) ob = M.op (v (some 0)) (v (some 1)))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨ddSplitFormulaG G tf xf df oa ob, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [ddSplitFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf, hxf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hg (v (some 1)) hy
    grind
  · by_cases hxy : v (some 0) = v (some 1)
    · have h4 := hdf v default hy hxy
      grind
    · by_cases hx : t (v (some 0))
      · have h5 := hoa v default hy hxy hx
        grind
      · have h6 := hob v default hy hxy hx
        grind

/-- `T` is the image, the diagonal of `S` is read off any column of `T`, and off it the read is
`oa` on `T × S` and `ob` on `S × S`. -/
theorem definable_graph_tcolGamma
    (oa ob : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0))
    (hoa : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G), ¬ t (v (some 1)) →
      v (some 0) ≠ v (some 1) → t (v (some 0)) →
      Term.realize (Sum.elim v xs) oa = M.op (v (some 0)) (v (some 1)))
    (hob : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G), ¬ t (v (some 1)) →
      v (some 0) ≠ v (some 1) → ¬ t (v (some 0)) →
      Term.realize (Sum.elim v xs) ob = M.op (v (some 0)) (v (some 1)))
    (him : ∀ y : G, (∃ p q : G, P.op p q = y) ↔ t y)
    (htim : ∀ a b : G, t (M.op a b))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y)
    (hdd : ∀ x c : G, ¬ t x → t c → P.op x c = M.op x x) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine definable_graph_ddSplitG imY imX tcolF oa ob
    (fun v xs ↦ (realize_imY v xs).trans (him _)) (fun v xs ↦ (realize_imX v xs).trans (him _))
    (fun v xs hy hxy ↦ ?_) hoa hob hin hg
  have hx : ¬ t (v (some 0)) := hxy ▸ hy
  rw [realize_tcolF]
  constructor
  · rintro ⟨p, q, h⟩
    rw [h, hdd _ _ hx ((him _).1 ⟨p, q, rfl⟩), hxy]
  · rintro h
    obtain ⟨p, q, hpq⟩ := (him (M.op (v (some 0)) (v (some 0)))).2 (htim _ _)
    exact ⟨p, q, by rw [h, ← hxy, hdd _ _ hx ((him _).1 ⟨p, q, rfl⟩)]⟩

/-- The same with the diagonal of `S` read off a *row* of `T`. -/
theorem definable_graph_trowGamma
    (oa ob : (MagmaLanguage[[(∅ : Set G)]]).Term (Option (Fin 2) ⊕ Fin 0))
    (hoa : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G), ¬ t (v (some 1)) →
      v (some 0) ≠ v (some 1) → t (v (some 0)) →
      Term.realize (Sum.elim v xs) oa = M.op (v (some 0)) (v (some 1)))
    (hob : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G), ¬ t (v (some 1)) →
      v (some 0) ≠ v (some 1) → ¬ t (v (some 0)) →
      Term.realize (Sum.elim v xs) ob = M.op (v (some 0)) (v (some 1)))
    (him : ∀ y : G, (∃ p q : G, P.op p q = y) ↔ t y)
    (htim : ∀ a b : G, t (M.op a b))
    (hin : ∀ a b : G, t b → M.op a b = M.op b b)
    (hg : ∀ y : G, t y → P.op y y = M.op y y)
    (hdd : ∀ x c : G, ¬ t x → t c → P.op c x = M.op x x) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine definable_graph_ddSplitG imY imX trowF oa ob
    (fun v xs ↦ (realize_imY v xs).trans (him _)) (fun v xs ↦ (realize_imX v xs).trans (him _))
    (fun v xs hy hxy ↦ ?_) hoa hob hin hg
  have hx : ¬ t (v (some 0)) := hxy ▸ hy
  rw [realize_trowF]
  constructor
  · rintro ⟨p, q, h⟩
    rw [h, hdd _ _ hx ((him _).1 ⟨p, q, rfl⟩), hxy]
  · rintro h
    obtain ⟨p, q, hpq⟩ := (him (M.op (v (some 0)) (v (some 0)))).2 (htim _ _)
    exact ⟨p, q, by rw [h, ← hxy, hdd _ _ hx ((him _).1 ⟨p, q, rfl⟩)]⟩

end Reverse

/-! ### Packaging

A concrete operation never has to name `T`: `im □ = T` is a *consequence* of the cell-level facts
the reverse read already asks for. Given `y ∈ T` the source writes it as `M p q`; if `q ∈ T` then
`y = M q q = □ q q` by the diagonal clause, and otherwise `M p q` sits in a column of `S`, which the
off-`T` clause copies. So an operation has to supply only

* that every value of `□` lands in `T`,
* that `□` keeps `γ` on the diagonal of `T`,
* and how `□` reads the columns of `S`,

each of which is decided by walking its tree. -/

section Ops

variable (M : Magma G) (K : GKer M)

/-- `T` is the image, as a rewrite for the `apply` lemmas. -/
theorem gtimex (w : G) : (∃ p q : G, M.op p q = w) ↔ K.t w :=
  ⟨fun ⟨p, q, e⟩ ↦ e ▸ K.tim p q, K.tex w⟩

include K in
/-- The image of the new operation is `T` again, for free. -/
theorem gker_image {P : Magma G}
    (hle : ∀ a b : G, K.t (P.op a b))
    (hg : ∀ y : G, K.t y → P.op y y = M.op y y)
    (hout : ∀ x y : G, ¬ K.t y → ∃ a b : G, P.op a b = M.op x y) (y : G) :
    (∃ a b : G, P.op a b = y) ↔ K.t y := by
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨a, b, rfl⟩
    exact hle a b
  · obtain ⟨p, q, hpq⟩ := K.tex y hy
    by_cases hq : K.t q
    · exact ⟨q, q, by rw [hg q hq, ← K.hin p q hq, hpq]⟩
    · obtain ⟨a, b, hab⟩ := hout p q hq
      exact ⟨a, b, by rw [hab, hpq]⟩

include K in
/-- The source itself on the columns of `S`. -/
theorem structuralOn_selfGamma (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hle : ∀ a b : G, K.t ((q.magma M).op a b))
    (hg : ∀ y : G, K.t y → (q.magma M).op y y = M.op y y)
    (hout : ∀ x y : G, ¬ K.t y → (q.magma M).op x y = M.op x y) :
    L.StructuralOnMagma M :=
  ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_selfGamma (gker_image M K hle hg (fun x y hy ↦ ⟨x, y, hout x y hy⟩)) K.hin
      hg hout⟩

include K in
/-- The source transposed on the columns of `S`. -/
theorem structuralOn_swapGamma (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hle : ∀ a b : G, K.t ((q.magma M).op a b))
    (hg : ∀ y : G, K.t y → (q.magma M).op y y = M.op y y)
    (hout : ∀ x y : G, ¬ K.t y → (q.magma M).op y x = M.op x y) :
    L.StructuralOnMagma M :=
  ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_swapGammaG imY
      (fun v xs ↦ (realize_imY (P := q.magma M) v xs).trans
        (gker_image M K hle hg (fun x y hy ↦ ⟨y, x, hout x y hy⟩) _))
      K.hin hg hout⟩

include K in
/-- Transposed on `T × S`, direct on `S × S`. -/
theorem structuralOn_splitGamma (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hle : ∀ a b : G, K.t ((q.magma M).op a b))
    (hg : ∀ y : G, K.t y → (q.magma M).op y y = M.op y y)
    (hts : ∀ x y : G, K.t x → ¬ K.t y → (q.magma M).op y x = M.op x y)
    (hss : ∀ x y : G, ¬ K.t x → ¬ K.t y → (q.magma M).op x y = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have him := gker_image M K hle hg (fun x y hy ↦
    if hx : K.t x then ⟨y, x, hts x y hx hy⟩ else ⟨x, y, hss x y hx hy⟩)
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_splitGammaG imY imX (fun v xs ↦ (realize_imY (P := q.magma M) v xs).trans (him _))
      (fun v xs ↦ (realize_imX (P := q.magma M) v xs).trans (him _)) K.hin hg hts hss⟩

include K in
/-- Direct on `T × S`, transposed on `S × S`. -/
theorem structuralOn_splitGamma' (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hle : ∀ a b : G, K.t ((q.magma M).op a b))
    (hg : ∀ y : G, K.t y → (q.magma M).op y y = M.op y y)
    (hts : ∀ x y : G, K.t x → ¬ K.t y → (q.magma M).op x y = M.op x y)
    (hss : ∀ x y : G, ¬ K.t x → ¬ K.t y → (q.magma M).op y x = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have him := gker_image M K hle hg (fun x y hy ↦
    if hx : K.t x then ⟨x, y, hts x y hx hy⟩ else ⟨y, x, hss x y hx hy⟩)
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_splitGammaG' imY imX (fun v xs ↦ (realize_imY (P := q.magma M) v xs).trans (him _))
      (fun v xs ↦ (realize_imX (P := q.magma M) v xs).trans (him _)) K.hin hg hts hss⟩

include K in
/-- The diagonal of `S` read off a column of `T`, and the source itself everywhere else. -/
theorem structuralOn_tcolGamma (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hle : ∀ a b : G, K.t ((q.magma M).op a b))
    (hg : ∀ y : G, K.t y → (q.magma M).op y y = M.op y y)
    (hdd : ∀ x c : G, ¬ K.t x → K.t c → (q.magma M).op x c = M.op x x)
    (hout : ∀ x y : G, ¬ K.t y → x ≠ y → (q.magma M).op x y = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have him := gker_image M K hle hg (fun x y hy ↦
    if hxy : x = y then ⟨x, M.op x x, by subst hxy; exact hdd _ _ hy (K.tim x x)⟩
    else ⟨x, y, hout x y hy hxy⟩)
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_tcolGamma (ap G x0 y0) (ap G x0 y0)
      (fun v xs hy hxy _ ↦ by simpa [x0, y0, realize_ap] using hout _ _ hy hxy)
      (fun v xs hy hxy _ ↦ by simpa [x0, y0, realize_ap] using hout _ _ hy hxy)
      him K.tim K.hin hg hdd⟩

include K in
/-- The same, but with the source transposed on `S × S`. -/
theorem structuralOn_tcolGamma' (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hle : ∀ a b : G, K.t ((q.magma M).op a b))
    (hg : ∀ y : G, K.t y → (q.magma M).op y y = M.op y y)
    (hdd : ∀ x c : G, ¬ K.t x → K.t c → (q.magma M).op x c = M.op x x)
    (hts : ∀ x y : G, K.t x → ¬ K.t y → (q.magma M).op x y = M.op x y)
    (hss : ∀ x y : G, ¬ K.t x → ¬ K.t y → x ≠ y → (q.magma M).op y x = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have him := gker_image M K hle hg (fun x y hy ↦
    if hxy : x = y then ⟨x, M.op x x, by subst hxy; exact hdd _ _ hy (K.tim x x)⟩
    else if hx : K.t x then ⟨x, y, hts x y hx hy⟩ else ⟨y, x, hss x y hx hy hxy⟩)
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_tcolGamma (ap G x0 y0) (ap G y0 x0)
      (fun v xs hy _ hx ↦ by simpa [x0, y0, realize_ap] using hts _ _ hx hy)
      (fun v xs hy hxy hx ↦ by simpa [x0, y0, realize_ap] using hss _ _ hx hy hxy)
      him K.tim K.hin hg hdd⟩

include K in
/-- The diagonal of `S` read off a row of `T`, and the source transposed everywhere else. -/
theorem structuralOn_trowGamma (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hle : ∀ a b : G, K.t ((q.magma M).op a b))
    (hg : ∀ y : G, K.t y → (q.magma M).op y y = M.op y y)
    (hdd : ∀ x c : G, ¬ K.t x → K.t c → (q.magma M).op c x = M.op x x)
    (hout : ∀ x y : G, ¬ K.t y → x ≠ y → (q.magma M).op y x = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have him := gker_image M K hle hg (fun x y hy ↦
    if hxy : x = y then ⟨M.op x x, x, by subst hxy; exact hdd _ _ hy (K.tim x x)⟩
    else ⟨y, x, hout x y hy hxy⟩)
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_trowGamma (ap G y0 x0) (ap G y0 x0)
      (fun v xs hy hxy _ ↦ by simpa [x0, y0, realize_ap] using hout _ _ hy hxy)
      (fun v xs hy hxy _ ↦ by simpa [x0, y0, realize_ap] using hout _ _ hy hxy)
      him K.tim K.hin hg hdd⟩

include K in
/-- The same, but with the source direct on `S × S`. -/
theorem structuralOn_trowGamma' (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hle : ∀ a b : G, K.t ((q.magma M).op a b))
    (hg : ∀ y : G, K.t y → (q.magma M).op y y = M.op y y)
    (hdd : ∀ x c : G, ¬ K.t x → K.t c → (q.magma M).op c x = M.op x x)
    (hts : ∀ x y : G, K.t x → ¬ K.t y → (q.magma M).op y x = M.op x y)
    (hss : ∀ x y : G, ¬ K.t x → ¬ K.t y → x ≠ y → (q.magma M).op x y = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have him := gker_image M K hle hg (fun x y hy ↦
    if hxy : x = y then ⟨M.op x x, x, by subst hxy; exact hdd _ _ hy (K.tim x x)⟩
    else if hx : K.t x then ⟨y, x, hts x y hx hy⟩ else ⟨x, y, hss x y hx hy hxy⟩)
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_trowGamma (ap G y0 x0) (ap G x0 y0)
      (fun v xs hy _ hx ↦ by simpa [x0, y0, realize_ap] using hts _ _ hx hy)
      (fun v xs hy hxy hx ↦ by simpa [x0, y0, realize_ap] using hss _ _ hx hy hxy)
      him K.tim K.hin hg hdd⟩

end Ops

end Quad4374
