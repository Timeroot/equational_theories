import equational_theories.Definability.Clone
import equational_theories.Definability.FiniteFlavour
import equational_theories.Definability.Regular

/-!
# Clones of products: the certificate a single magma cannot give

A clone certificate refutes `L` from `L'` by exhibiting one model of `L'` no term of which satisfies
`L`. Plenty of open cells have no such model at all: every model of `L'` in the bank has *some* term
that works, but never the same term twice. That is exactly what a product settles. A term function
on `∏ⱼ Aⱼ` is the tuple of its component term functions, so

    the product satisfies `L` at the term `w`  ↔  every factor does,

and a family of models with no common witness has a product with no witness at all. `Definability/
CloneBig.lean` needed a `1304`-operation clone on `Fin 6` to close one cell; a product of four
models of sizes `2, 2, 4, 8` closes cells that no single model in a bank of fifty thousand does.

The obstacle is writing it down. The product of those four is a magma on `128` points, its clone
runs to several hundred operations, and listing them as tables is nine megabytes of data and a
`native_decide` a hundred times over budget. The fix is that none of it has to be listed on the
product at all:

* the carrier is `∀ j, A j`, and an operation of the clone is a *tuple of factor operations*, so
  `F : κ → ∀ j, A j → A j → A j` is all the data there is -- `k · Σⱼ |Aⱼ|²` bytes, not `k · (∏ⱼ
  |Aⱼ|)²`;
* being a clone family is checked coordinatewise, `Magma.piMagma_isCloneFamily`: `k²·Σⱼ|Aⱼ|²` index
  comparisons rather than `k²·(∏ⱼ|Aⱼ|)²`;
* the source law is checked coordinatewise as well, `Magma.satisfies_piMagma`, because equational
  laws are preserved by products;
* and the target law never has to be evaluated on the product either: a coordinate projection is a
  surjective homomorphism, `Magma.satisfies_of_satisfies_piMagma`, so a single factor in which the
  operation `F i j` fails `L` is enough to kill the whole tuple `F i`.

So the certificate is: the factor operations, the tuples, the composition table, and for each tuple
one coordinate that fails the target. Everything in it is decidable at the size of the factors.

The index type `κ` of the family is the *reachable* set of tuples, not all of `∏ⱼ κⱼ`. That matters:
the family of all tuples is closed under composition too, but it contains the tuple that takes a
witness in each factor separately, and would refute nothing. Cf. `Definability/Clone.lean` on why a
clone family may be any superset of the clone and why smaller is stronger.
-/

open Law Law.MagmaLaw FreeMagma

namespace Magma

-- `Magma.IsCloneFamily` lives over a carrier in `Type`, and the product carrier is
-- `∀ j, A j`, so both the index and the factors have to stay there
variable {ι : Type} {α : Type*} {A : ι → Type}

/-- The coordinatewise magma on a dependent product of carriers. -/
@[implicit_reducible]
def piMagma (f : ∀ j, A j → A j → A j) : Magma (∀ j, A j) := ⟨fun x y j ↦ f j (x j) (y j)⟩

@[simp]
theorem piMagma_op (f : ∀ j, A j → A j → A j) (x y : ∀ j, A j) (j : ι) :
    (piMagma f).op x y j = f j (x j) (y j) := rfl

/-- Evaluation in a product is evaluation in each factor. This is the whole content of the file;
everything below is a corollary. -/
theorem evalInMagma_piMagma (f : ∀ j, A j → A j → A j) (φ : α → ∀ j, A j) (j : ι) :
    ∀ t : FreeMagma α,
      @evalInMagma α _ (piMagma f) φ t j = @evalInMagma α _ ⟨f j⟩ (fun a ↦ φ a j) t
  | .Leaf _ => rfl
  | .Fork l r => by
    show f j _ _ = f j _ _
    rw [evalInMagma_piMagma f φ j l, evalInMagma_piMagma f φ j r]

/-- A law true in every factor is true in the product: equational laws are preserved by products,
which is what lets the source law be checked one small factor at a time. -/
theorem satisfies_piMagma {f : ∀ j, A j → A j → A j} {L : MagmaLaw α}
    (h : ∀ j, @satisfies α _ (⟨f j⟩ : Magma (A j)) L) : @satisfies α _ (piMagma f) L :=
  fun φ ↦ funext fun j ↦ by
    simpa [satisfiesPhi, evalInMagma_piMagma] using h j (fun a ↦ φ a j)

/-- A law true in the product is true in each factor: the coordinate projections are surjective
homomorphisms. This is the direction the refutation uses -- one bad coordinate kills the tuple. -/
theorem satisfies_of_satisfies_piMagma [DecidableEq ι] [∀ j, Inhabited (A j)]
    {f : ∀ j, A j → A j → A j} {L : MagmaLaw α} (j : ι)
    (h : @satisfies α _ (piMagma f) L) : @satisfies α _ (⟨f j⟩ : Magma (A j)) L := fun φ ↦ by
  have := congrFun (h fun a ↦ Function.update (fun j' ↦ (default : A j')) j (φ a)) j
  simpa [satisfiesPhi, evalInMagma_piMagma] using this

/-- **The product clone family.** A set of tuples of factor operations that contains the two
projections and is closed under coordinatewise composition is a clone family for the product magma.
Each hypothesis is quantified over one factor at a time, so all three are decidable at the size of
the factors rather than the size of the product. -/
theorem piMagma_isCloneFamily {κ : Type*} {op : ∀ j, A j → A j → A j}
    {F : κ → ∀ j, A j → A j → A j} {i₁ i₂ : κ} {c : κ → κ → κ}
    (h₁ : ∀ j x y, F i₁ j x y = x) (h₂ : ∀ j x y, F i₂ j x y = y)
    (hc : ∀ i i' j x y, F (c i i') j x y = op j (F i j x y) (F i' j x y)) :
    (piMagma op).IsCloneFamily (fun i ↦ piMagma (F i)) i₁ i₂ c where
  fst x y := funext fun j ↦ h₁ j (x j) (y j)
  snd x y := funext fun j ↦ h₂ j (x j) (y j)
  comp i i' x y := funext fun j ↦ hc i i' j (x j) (y j)

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- **The product certificate.** Given finitely many finite models `⟨op j⟩` of `L'`, a set of tuples
of operations closed under coordinatewise composition and containing the projections, and for each
tuple one coordinate whose operation fails `L`, the law `L` is not term-definable from `L'` over
finite magmas -- hence not over all magmas either.

Nothing here is stated on the product. A certificate is: the factor tables, the tuple table, the
composition table, and the list of bad coordinates. -/
theorem not_termDefinableFromFin_of_piClone {ι : Type} [Finite ι] [DecidableEq ι]
    {A : ι → Type} [∀ j, Finite (A j)] [∀ j, Inhabited (A j)] (op : ∀ j, A j → A j → A j)
    (hM : ∀ j, @satisfies _ _ (⟨op j⟩ : Magma (A j)) L')
    {κ : Type*} (F : κ → ∀ j, A j → A j → A j) (i₁ i₂ : κ) (c : κ → κ → κ)
    (h₁ : ∀ j x y, F i₁ j x y = x) (h₂ : ∀ j x y, F i₂ j x y = y)
    (hc : ∀ i i' j x y, F (c i i') j x y = op j (F i j x y) (F i' j x y))
    (hL : ∀ i, ∃ j, ¬ @satisfies _ _ (⟨F i j⟩ : Magma (A j)) L) :
    ¬ L.TermDefinableFromFin L' :=
  not_termDefinableFromFin_of_clone (Magma.piMagma op) (Magma.satisfies_piMagma hM)
    (Magma.piMagma_isCloneFamily h₁ h₂ hc)
    fun i h ↦ (hL i).elim fun _ hj ↦ hj (Magma.satisfies_of_satisfies_piMagma _ h)

end Law.MagmaLaw
