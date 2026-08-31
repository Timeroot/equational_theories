import equational_theories.Definability.CaseSplit

/-!
# Division as a first-order structural witness, over all magmas

`Definability/DivisionStructural.lean` makes the two divisions *terms*, and pays for it with
finiteness: a translation of a finite set is a permutation, so `L_a⁻¹ = L_a^N` for an exponent `N`
read off the carrier. Over all magmas that exponent is unavailable and the route stops.

It does not have to be a term. `Law.MagmaLaw.StructuralFrom` asks for two **first-order**
definitions, and the division is the cheapest pair of those there is. If every left translation of
`M` is a bijection then `x \ y` is the unique `z` with `x ◇ z = y`, so

* the graph of `\` is `{(x, y, z) : x ◇ z = y}`, an atomic formula of `M`, and
* the graph of `◇` is `{(x, y, z) : x \ z = y}`, the *same* atomic formula read in `\`.

Nothing is searched for and nothing is iterated: one formula, `DivisionFO.ldivFormula`, is both
halves, because inverting a bijection is an involution. The right division is the mirror image,
`DivisionFO.rdivFormula`.

What the source has to supply is the bijectivity, and that is where this differs from the finite
route in kind rather than in degree. Surjectivity of `L_a` is an equational consequence, so it
always has a single term witness `w` with `x ◇ w(x, y) = y`; injectivity is a Horn clause and has
none. When both `x ◇ w(x, y) = y` and `w(x, x ◇ y) = y` are equational consequences of the source
the division is that term and `LDiv` is built by hand; when only bijectivity is provable, `LDiv.of`
builds it by choice.

## Main results

* `DivisionFO.LDiv`, `DivisionFO.RDiv`: a division, as data.
* `DivisionFO.LDiv.of`, `DivisionFO.RDiv.of`: one built from surjectivity and injectivity.
* `DivisionFO.structuralOn_ldiv`, `DivisionFO.structuralOn_rdiv`: both halves of
  `StructuralOnMagma`, from a division and the law it satisfies.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw

variable {G : Type}

namespace DivisionFO

/-- The `MagmaLanguage` structure of the ambient magma, as an instance so that `Term.realize` and
`Formula.Realize` can be written without a pile of `@`s. -/
local instance instFOStructure [M : Magma G] : MagmaLanguage.Structure G := M.FOStructure

/-- `a ◇ b`, as a term of the magma language. -/
def ap (G : Type) {α : Type} (a b : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    (MagmaLanguage[[(∅ : Set G)]]).Term α :=
  Functions.apply₂ (L := MagmaLanguage[[(∅ : Set G)]]) (Sum.inl ()) a b

@[simp] theorem realize_ap [Magma G] {α : Type} (v : α → G)
    (a b : (MagmaLanguage[[(∅ : Set G)]]).Term α) :
    Term.realize v (ap G a b) = Magma.op (Term.realize v a) (Term.realize v b) := rfl

/-! ### The left division -/

/-- A left division, as data: `d x y` is the solution of `x ◇ ? = y`, and it is the only one. -/
structure LDiv (M : Magma G) where
  /-- the division -/
  d : G → G → G
  /-- it solves the equation -/
  inv : ∀ x y : G, M.op x (d x y) = y
  /-- and it is the only solution -/
  can : ∀ x y : G, d x (M.op x y) = y

/-- A left division out of surjectivity and injectivity of the left translations. -/
noncomputable def LDiv.of (M : Magma G) (hs : ∀ x y : G, ∃ z : G, M.op x z = y)
    (hi : ∀ x y z : G, M.op x y = M.op x z → y = z) : LDiv M where
  d x y := (hs x y).choose
  inv x y := (hs x y).choose_spec
  can x y := hi x _ _ ((hs x (M.op x y)).choose_spec)

/-- The magma the division is. -/
@[implicit_reducible]
def LDiv.magma {M : Magma G} (K : LDiv M) : Magma G := ⟨K.d⟩

@[simp] theorem LDiv.magma_op {M : Magma G} (K : LDiv M) (x y : G) :
    K.magma.op x y = K.d x y := rfl

/-- `x ◇ z = y`, in the output variable `none` and the arguments `some 0`, `some 1`. Read in the
source it cuts out the graph of the left division; read in the left division it cuts out the graph
of the source. -/
def ldivFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.equal (ap G (var (some 0)) (var none)) (var (some 1))

@[simp] theorem realize_ldivFormula [M : Magma G] (v : Option (Fin 2) → G) :
    (ldivFormula G).Realize v ↔ M.op (v (some 0)) (v none) = v (some 1) := by
  simp [ldivFormula, Formula.realize_equal]

/-- **The forward half.** The graph of the division is an atomic formula of the source. -/
theorem definable_graph_ldiv (M : Magma G) (K : LDiv M) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ K.magma.Graph := by
  refine ⟨ldivFormula G, Set.ext fun v ↦ ?_⟩
  show K.d (v (some 0)) (v (some 1)) = v none ↔ _
  rw [Set.mem_setOf_eq, @realize_ldivFormula _ M v]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]; exact K.inv _ _
  · rw [← h]; exact K.can _ _

/-- **The reverse half.** The graph of the source is the same atomic formula, read in the
division. -/
theorem definable_graph_of_ldiv (M : Magma G) (K : LDiv M) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage K.magma.FOStructure _ M.Graph := by
  refine ⟨ldivFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  rw [Set.mem_setOf_eq, @realize_ldivFormula _ K.magma v]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]; exact K.can _ _
  · rw [← h]; exact K.inv _ _

/-- **Both halves of `StructuralOnMagma`, from a left division.** -/
theorem structuralOn_ldiv (M : Magma G) (K : LDiv M) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G K.magma L) : L.StructuralOnMagma M :=
  ⟨K.magma, hL, definable_graph_ldiv M K, definable_graph_of_ldiv M K⟩

/-! ### The right division -/

/-- A right division, as data: `d x y` is the solution of `? ◇ y = x`, and it is the only one. -/
structure RDiv (M : Magma G) where
  /-- the division -/
  d : G → G → G
  /-- it solves the equation -/
  inv : ∀ x y : G, M.op (d x y) y = x
  /-- and it is the only solution -/
  can : ∀ x y : G, d (M.op x y) y = x

/-- A right division out of surjectivity and injectivity of the right translations. -/
noncomputable def RDiv.of (M : Magma G) (hs : ∀ x y : G, ∃ z : G, M.op z y = x)
    (hi : ∀ x y z : G, M.op y x = M.op z x → y = z) : RDiv M where
  d x y := (hs x y).choose
  inv x y := (hs x y).choose_spec
  can x y := hi y _ _ ((hs (M.op x y) y).choose_spec)

/-- The magma the division is. -/
@[implicit_reducible]
def RDiv.magma {M : Magma G} (K : RDiv M) : Magma G := ⟨K.d⟩

@[simp] theorem RDiv.magma_op {M : Magma G} (K : RDiv M) (x y : G) :
    K.magma.op x y = K.d x y := rfl

/-- `z ◇ y = x`, in the output variable `none` and the arguments `some 0`, `some 1`. -/
def rdivFormula (G : Type) : (MagmaLanguage[[(∅ : Set G)]]).Formula (Option (Fin 2)) :=
  Term.equal (ap G (var none) (var (some 1))) (var (some 0))

@[simp] theorem realize_rdivFormula [M : Magma G] (v : Option (Fin 2) → G) :
    (rdivFormula G).Realize v ↔ M.op (v none) (v (some 1)) = v (some 0) := by
  simp [rdivFormula, Formula.realize_equal]

/-- **The forward half**, on the right. -/
theorem definable_graph_rdiv (M : Magma G) (K : RDiv M) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ K.magma.Graph := by
  refine ⟨rdivFormula G, Set.ext fun v ↦ ?_⟩
  show K.d (v (some 0)) (v (some 1)) = v none ↔ _
  rw [Set.mem_setOf_eq, @realize_rdivFormula _ M v]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]; exact K.inv _ _
  · rw [← h]; exact K.can _ _

/-- **The reverse half**, on the right. -/
theorem definable_graph_of_rdiv (M : Magma G) (K : RDiv M) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage K.magma.FOStructure _ M.Graph := by
  refine ⟨rdivFormula G, Set.ext fun v ↦ ?_⟩
  show M.op (v (some 0)) (v (some 1)) = v none ↔ _
  rw [Set.mem_setOf_eq, @realize_rdivFormula _ K.magma v]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]; exact K.can _ _
  · rw [← h]; exact K.inv _ _

/-- **Both halves of `StructuralOnMagma`, from a right division.** -/
theorem structuralOn_rdiv (M : Magma G) (K : RDiv M) {β : Type*} {L : Law.MagmaLaw β}
    (hL : @satisfies _ G K.magma L) : L.StructuralOnMagma M :=
  ⟨K.magma, hL, definable_graph_rdiv M K, definable_graph_of_rdiv M K⟩

end DivisionFO
