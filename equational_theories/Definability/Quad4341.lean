import equational_theories.Definability.Quad4351

/-!
# The square-*row* family: a product forgets which square it is given

Equation `4341` is `x ◇ (y ◇ y) = x ◇ (z ◇ z)`: a product depends only on its *left* argument as
soon as its right argument is a square. Writing `D := {y ◇ y : y}` and `S := G ∖ D`, a model is

* a set `G`, a subset `D`, a map `κ : G → G`, a map `γ : D → D` and a free `h : G × S → G`,
* the operation `x ◇ y = κ x` for `y ∈ D` and `x ◇ y = h x y` for `y ∈ S`,

subject to `γ = κ|D` landing in `D` and `{h y y : y ∈ S} ∪ γ(D) = D`, which is what makes `D` the
square set. Equivalently `κ x = x ◇ (x ◇ x)`, since `x ◇ x` is a square.

This is the transpose in spirit of `Quad4351` — there the constant of a `D`-column was fixed, here
it varies with the row — but it is *not* the transpose as a law: `4351` and `4341` are unrelated in
the implication order, and their families overlap only partly. Of the hundred and sixteen open
sources that imply `4341` up to duality, seventy four are reached by neither `4351` nor `4374`.

The consequence for the reverse reads is the whole content of this file. A read of `4351` recovers a
`D`-column cell from the *diagonal* cell `(y, y)`, which every read keeps. A read of `4341` has to
recover `x ◇ y = κ x` from a cell of row `x`, and the only one available is `(x, x ◇ x)` — the
column of `x`'s own square. So each read carries one more hypothesis than its `4351` counterpart:

* `hk : ∀ x, x □ (x □ x) = x ◇ (x ◇ x)` for the reads whose off-`D` block is direct, and
* `hk : ∀ x, (x □ x) □ x = x ◇ (x ◇ x)` for the reads whose off-`D` block is transposed, which have
  already spent the cell `(x, x □ x)` on the source and must use `(x □ x, x)` instead.

`D` is named by `Quad4351.sqY`, exactly as there and for exactly the same reason: every read keeps
the diagonal.

## Main results

* `Quad4341.RKer`: the structure of a model of `4341`.
* `Quad4341.rkernel`: reading it off the law.
* `Quad4341.structuralOn_selfKappaD` and friends: the four reads, with `D` named for free.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma Quad4274 Quad4374

universe u

variable {G : Type}

namespace Quad4341

/-- The `MagmaLanguage` structure of the ambient magma, as an instance. -/
local instance instFOStructure [M : Magma G] : MagmaLanguage.Structure G := M.FOStructure

/-! ### The structure of a model of `4341` -/

/-- The data a model of `4341` amounts to: the square set `d`, and the one fact that says a
product's right argument is forgotten as soon as it is a square. -/
structure RKer (M : Magma G) where
  /-- the set of squares -/
  d : G → Prop
  /-- every square is in it -/
  dsq : ∀ a : G, d (M.op a a)
  /-- and conversely -/
  dex : ∀ y : G, d y → ∃ a : G, M.op a a = y
  /-- on the squares the right argument is forgotten, so the value is the row's own constant -/
  hin : ∀ a b : G, d b → M.op a b = M.op a (M.op a a)

/-- Reading the kernel off the law. -/
def rkernel (M : Magma G) (h : ∀ x y z : G, M.op x (M.op y y) = M.op x (M.op z z)) : RKer M where
  d y := ∃ a : G, M.op a a = y
  dsq a := ⟨a, rfl⟩
  dex _ hy := hy
  hin a b := by
    rintro ⟨p, rfl⟩
    exact h a p a

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

variable {M P : Magma G} {t : G → Prop}

/-- `x □ (x □ x)` when `y` is a square, and `x □ y` otherwise. -/
def selfKappaFormulaG (G : Type) (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G x0 (ap G x0 x0))) ⊔ (∼tf ⊓ Term.bdEqual z0 (ap G x0 y0))

/-- The simplest read: `x ◇ y` is `x □ (x □ x)` when `y ∈ D`, and `x □ y` otherwise, where `D` is
cut out by whichever formula `tf` the operation admits. -/
theorem definable_graph_selfKappaG
    (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hin : ∀ a b : G, t b → M.op a b = M.op a (M.op a a))
    (hd : ∀ y : G, P.op y y = M.op y y)
    (hk : ∀ x : G, P.op x (M.op x x) = M.op x (M.op x x))
    (hout : ∀ x y : G, ¬ t y → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨selfKappaFormulaG G tf, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [selfKappaFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hd (v (some 0))
    have h4 := hk (v (some 0))
    grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy
    grind

/-- The same read with the columns of `S` transposed. The `D`-branch changes with it: the cell
`(x, x □ x)` now belongs to the source, so the row's constant is read off `(x □ x, x)`. -/
def swapKappaFormulaG (G : Type) (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G (ap G x0 x0) x0)) ⊔ (∼tf ⊓ Term.bdEqual z0 (ap G y0 x0))

/-- `x ◇ y` is `(x □ x) □ x` when `y ∈ D`, and `y □ x` otherwise. -/
theorem definable_graph_swapKappaG
    (tf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hin : ∀ a b : G, t b → M.op a b = M.op a (M.op a a))
    (hd : ∀ y : G, P.op y y = M.op y y)
    (hk : ∀ x : G, P.op (M.op x x) x = M.op x (M.op x x))
    (hout : ∀ x y : G, ¬ t y → P.op y x = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨swapKappaFormulaG G tf, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [swapKappaFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hd (v (some 0))
    have h4 := hk (v (some 0))
    grind
  · have h2 := hout (v (some 0)) (v (some 1)) hy
    grind

/-- The read that transposes only where the first argument is in `D`. -/
def splitKappaFormulaG (G : Type)
    (tf xf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G (ap G x0 x0) x0))
    ⊔ ((∼tf ⊓ xf) ⊓ Term.bdEqual z0 (ap G y0 x0))
    ⊔ ((∼tf ⊓ ∼xf) ⊓ Term.bdEqual z0 (ap G x0 y0))

/-- `x ◇ y` is `(x □ x) □ x` on `D`; off it the cell is `y □ x` when `x ∈ D` and `x □ y` when
`x ∉ D`. The diagonal of `S` falls in the last branch, where the read is direct. -/
theorem definable_graph_splitKappaG
    (tf xf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hxf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize xf v xs ↔ t (v (some 0)))
    (hin : ∀ a b : G, t b → M.op a b = M.op a (M.op a a))
    (hd : ∀ y : G, P.op y y = M.op y y)
    (hk : ∀ x : G, P.op (M.op x x) x = M.op x (M.op x x))
    (hts : ∀ x y : G, t x → ¬ t y → P.op y x = M.op x y)
    (hss : ∀ x y : G, ¬ t x → ¬ t y → P.op x y = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨splitKappaFormulaG G tf xf, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [splitKappaFormulaG, Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf, hxf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hd (v (some 0))
    have h4 := hk (v (some 0))
    grind
  · by_cases hx : t (v (some 0))
    · have h2 := hts (v (some 0)) (v (some 1)) hx hy
      grind
    · have h2 := hss (v (some 0)) (v (some 1)) hx hy
      grind

/-- The read that transposes only where the first argument is *outside* `D`. -/
def splitKappaFormulaG' (G : Type)
    (tf xf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2))) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  (tf ⊓ Term.bdEqual z0 (ap G x0 (ap G x0 x0)))
    ⊔ ((∼tf ⊓ xf) ⊓ Term.bdEqual z0 (ap G x0 y0))
    ⊔ ((∼tf ⊓ ∼xf) ⊓ Term.bdEqual z0 (ap G y0 x0))

/-- The mirror of `definable_graph_splitKappaG`: `x □ y` when `x ∈ D` and `y □ x` when `x ∉ D`.
Here the direct block keeps `(x, x □ x)` free of the source only when `x ∈ D`, but that is enough:
the `D`-branch reads the row constant off `(x, x □ x)` and the two clauses never meet. -/
theorem definable_graph_splitKappaG'
    (tf xf : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)))
    (htf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize tf v xs ↔ t (v (some 1)))
    (hxf : ∀ (v : Option (Fin 2) → G) (xs : Fin 0 → G),
      BoundedFormula.Realize xf v xs ↔ t (v (some 0)))
    (hin : ∀ a b : G, t b → M.op a b = M.op a (M.op a a))
    (hd : ∀ y : G, P.op y y = M.op y y)
    (hk : ∀ x : G, P.op x (M.op x x) = M.op x (M.op x x))
    (hts : ∀ x y : G, t x → ¬ t y → P.op x y = M.op x y)
    (hss : ∀ x y : G, ¬ t x → ¬ t y → P.op y x = M.op x y) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage P.FOStructure _ M.Graph := by
  refine ⟨splitKappaFormulaG' G tf xf, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  simp only [splitKappaFormulaG', Set.mem_setOf_eq, Formula.Realize, BoundedFormula.realize_sup,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    z0, x0, y0, realize_ap, Term.realize_var, Sum.elim_inl, htf, hxf]
  by_cases hy : t (v (some 1))
  · have h2 := hin (v (some 0)) (v (some 1)) hy
    have h3 := hd (v (some 0))
    have h4 := hk (v (some 0))
    grind
  · by_cases hx : t (v (some 0))
    · have h2 := hts (v (some 0)) (v (some 1)) hx hy
      grind
    · have h2 := hss (v (some 0)) (v (some 1)) hx hy
      grind

end Reverse

/-! ### Packaging

Every read is the identity on the diagonal, exactly as in `Quad4351`: on `D` because that is what
`hg` says, and off `D` because the off-`D` clause copies the source cell, which at `x = y` *is* the
diagonal one. So `Quad4351.sqY` cuts out `D` in the new magma with no work per operation. -/

section Ops

variable (M : Magma G) (K : RKer M)

include K in
/-- `D` is the square set of any operation that keeps the source's diagonal. -/
theorem rker_sq {P : Magma G} (hd : ∀ y : G, P.op y y = M.op y y) (y : G) :
    (∃ p : G, P.op p p = y) ↔ K.d y := by
  constructor
  · rintro ⟨p, rfl⟩
    exact (hd p) ▸ K.dsq p
  · rintro hy
    obtain ⟨p, hp⟩ := K.dex y hy
    exact ⟨p, (hd p).trans hp⟩

include K in
/-- The source itself on the columns of `S`. -/
theorem structuralOn_selfKappaD (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hg : ∀ y : G, K.d y → (q.magma M).op y y = M.op y y)
    (hk : ∀ x : G, (q.magma M).op x (M.op x x) = M.op x (M.op x x))
    (hout : ∀ x y : G, ¬ K.d y → (q.magma M).op x y = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have hd : ∀ y : G, (q.magma M).op y y = M.op y y :=
    fun y ↦ if hy : K.d y then hg y hy else hout y y hy
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_selfKappaG Quad4351.sqY
      (fun v xs ↦ (Quad4351.realize_sqY (P := q.magma M) v xs).trans (rker_sq M K hd _))
      K.hin hd hk hout⟩

include K in
/-- The source transposed on the columns of `S`. -/
theorem structuralOn_swapKappaD (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hg : ∀ y : G, K.d y → (q.magma M).op y y = M.op y y)
    (hk : ∀ x : G, (q.magma M).op (M.op x x) x = M.op x (M.op x x))
    (hout : ∀ x y : G, ¬ K.d y → (q.magma M).op y x = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have hd : ∀ y : G, (q.magma M).op y y = M.op y y :=
    fun y ↦ if hy : K.d y then hg y hy else hout y y hy
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_swapKappaG Quad4351.sqY
      (fun v xs ↦ (Quad4351.realize_sqY (P := q.magma M) v xs).trans (rker_sq M K hd _))
      K.hin hd hk hout⟩

include K in
/-- Transposed on `D × S`, direct on `S × S`. -/
theorem structuralOn_splitKappaD (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hg : ∀ y : G, K.d y → (q.magma M).op y y = M.op y y)
    (hk : ∀ x : G, (q.magma M).op (M.op x x) x = M.op x (M.op x x))
    (hts : ∀ x y : G, K.d x → ¬ K.d y → (q.magma M).op y x = M.op x y)
    (hss : ∀ x y : G, ¬ K.d x → ¬ K.d y → (q.magma M).op x y = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have hd : ∀ y : G, (q.magma M).op y y = M.op y y :=
    fun y ↦ if hy : K.d y then hg y hy else hss y y hy hy
  have hsq := rker_sq M K hd
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_splitKappaG Quad4351.sqY Quad4351.sqX
      (fun v xs ↦ (Quad4351.realize_sqY (P := q.magma M) v xs).trans (hsq _))
      (fun v xs ↦ (Quad4351.realize_sqX (P := q.magma M) v xs).trans (hsq _))
      K.hin hd hk hts hss⟩

include K in
/-- Direct on `D × S`, transposed on `S × S`. -/
theorem structuralOn_splitKappaD' (q : EOp) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G (q.magma M) L)
    (hg : ∀ y : G, K.d y → (q.magma M).op y y = M.op y y)
    (hk : ∀ x : G, (q.magma M).op x (M.op x x) = M.op x (M.op x x))
    (hts : ∀ x y : G, K.d x → ¬ K.d y → (q.magma M).op x y = M.op x y)
    (hss : ∀ x y : G, ¬ K.d x → ¬ K.d y → (q.magma M).op y x = M.op x y) :
    L.StructuralOnMagma M := by
  classical
  have hd : ∀ y : G, (q.magma M).op y y = M.op y y :=
    fun y ↦ if hy : K.d y then hg y hy else hss y y hy hy
  have hsq := rker_sq M K hd
  exact ⟨q.magma M, hL, EOp.definable_graph M q,
    definable_graph_splitKappaG' Quad4351.sqY Quad4351.sqX
      (fun v xs ↦ (Quad4351.realize_sqY (P := q.magma M) v xs).trans (hsq _))
      (fun v xs ↦ (Quad4351.realize_sqX (P := q.magma M) v xs).trans (hsq _))
      K.hin hd hk hts hss⟩

/-- `D` is the square set, as a rewrite for the `apply` lemmas. -/
theorem rsqex (w : G) : (∃ p : G, M.op p p = w) ↔ K.d w :=
  ⟨fun ⟨p, e⟩ ↦ e ▸ K.dsq p, K.dex w⟩

end Ops

end Quad4341
