import equational_theories.Definability.OrbitWitness
import Mathlib.GroupTheory.OrderOfElement

/-!
# Witnesses written with division

Thirty of the sources still open on the term-definability board have the chain shape
`x = h_k (⋯ (h_1 x) ⋯)` with every `h_i` a translation of the magma, and on a finite carrier that
forces every translation to be a bijection: the composite is the identity, so its innermost factor
is injective and its outermost surjective, and `Finite.injective_iff_surjective` closes the loop.
Such a magma is a quasigroup, and `Definability/PositiveTermsFin.lean` already exploits the weakest
consequence of this -- the cyclic rotations of the chain.

The strong consequence is that *division is a term*. A bijection of a finite set has finite order,
and the whole group `Equiv.Perm G` has exponent dividing its cardinality, so a single `N` inverts
every translation at once:

    a / b  =  (⋯ ((a ◇ b) ◇ b) ⋯ ◇ b)      and      a \ b  =  a ◇ (a ◇ ⋯ (a ◇ b))

with `N - 1` copies of `b`, respectively of `a`. Neither is a term of the source language for a
*fixed* `N`, which is why the plain flavour cannot see them; `N` is read off the carrier, which is
exactly the freedom `TermDefinableFromFin` grants and `TermDefinableFrom` does not.

So for a quasigroup-forcing source the witness may be sought in the clone of `◇`, `/` and `\`
rather than the clone of `◇` alone, and that is a strictly larger space -- the sweeps that
exhausted the latter say nothing about the former. `QTerm` is the syntax of that clone,
`QTerm.toBTerm` compiles it down to an honest magma term once `N` is known, and
`termDefinableFromFin_of_qterm` is the glue: give it a `QTerm`, a proof that the source forces both
translations injective, and a proof that the target holds of the term in any structure with
divisions, and it produces the cell.

The second obligation is unit equational -- source, rotations and the four quasigroup axioms
against a ground negated conjecture -- so it is a prover problem of exactly the kind
`Generated/VampireProven` already replays.
-/

open FirstOrder FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- The magma operation as a two-variable term. -/
private abbrev qmul (a b : BTerm G) : BTerm G := Functions.apply₂ (Sum.inl ()) a b

/-- `a ◇ b ◇ ⋯ ◇ b` with `n` copies of `b`: the term naming `n` right translations by `b`. -/
def riter (a b : BTerm G) : ℕ → BTerm G
  | 0 => a
  | n + 1 => qmul (riter a b n) b

/-- `a ◇ (a ◇ ⋯ (a ◇ b))` with `n` copies of `a`: the term naming `n` left translations by `a`. -/
def liter (a b : BTerm G) : ℕ → BTerm G
  | 0 => b
  | n + 1 => qmul a (liter a b n)

/-- The syntax of the clone of `◇`, `/` and `\`. -/
inductive QTerm where
  /-- One of the two variables. -/
  | var : Fin 2 → QTerm
  /-- A product. -/
  | op : QTerm → QTerm → QTerm
  /-- A right quotient: `rdv a b` is the solution of `? ◇ b = a`. -/
  | rdv : QTerm → QTerm → QTerm
  /-- A left quotient: `ldv a b` is the solution of `a ◇ ? = b`. -/
  | ldv : QTerm → QTerm → QTerm
  deriving Repr, DecidableEq

/-- The binary operation a `QTerm` denotes, given a multiplication and its two divisions. -/
def QTerm.eval (m rd ld : G → G → G) : QTerm → G → G → G
  | .var i => fun x y ↦ ![x, y] i
  | .op a b => fun x y ↦ m (a.eval m rd ld x y) (b.eval m rd ld x y)
  | .rdv a b => fun x y ↦ rd (a.eval m rd ld x y) (b.eval m rd ld x y)
  | .ldv a b => fun x y ↦ ld (a.eval m rd ld x y) (b.eval m rd ld x y)

/-- A `QTerm` compiled to a magma term: each division becomes `n` translations, which inverts the
translation exactly when `n + 1` is a period. -/
def QTerm.toBTerm (n : ℕ) : QTerm → BTerm G
  | .var i => Term.var i
  | .op a b => qmul (a.toBTerm n) (b.toBTerm n)
  | .rdv a b => riter (a.toBTerm n) (b.toBTerm n) n
  | .ldv a b => liter (a.toBTerm n) (b.toBTerm n) n

section Realize

variable (M : Magma G)

theorem bsem_qmul (a b : BTerm G) (x y : G) :
    bsem M (qmul a b) x y = M.op (bsem M a x y) (bsem M b x y) := rfl

theorem bsem_riter (a b : BTerm G) (n : ℕ) (x y : G) :
    bsem M (riter a b n) x y
      = (fun u ↦ M.op u (bsem M b x y))^[n] (bsem M a x y) := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ← ih]; rfl

theorem bsem_liter (a b : BTerm G) (n : ℕ) (x y : G) :
    bsem M (liter a b n) x y
      = (fun u ↦ M.op (bsem M a x y) u)^[n] (bsem M b x y) := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ← ih]; rfl

end Realize

/-- **One exponent inverts every bijection at once.** `Equiv.Perm G` is a finite group, so its
cardinality annihilates it, and any injective self-map of `G` is one of its elements. -/
theorem exists_uniform_period (G : Type) [Finite G] :
    ∃ N : ℕ, ∀ f : G → G, Function.Injective f → f^[N + 1] = id := by
  classical
  have : Fintype (Equiv.Perm G) := Fintype.ofFinite _
  refine ⟨Fintype.card (Equiv.Perm G) - 1, fun f hf ↦ ?_⟩
  have hb : Function.Bijective f := ⟨hf, Finite.injective_iff_surjective.mp hf⟩
  have hpos : 0 < Fintype.card (Equiv.Perm G) := Fintype.card_pos
  have hcard : Fintype.card (Equiv.Perm G) - 1 + 1 = Fintype.card (Equiv.Perm G) := by omega
  rw [hcard]
  have he : ⇑(Equiv.ofBijective f hb) = f := rfl
  have : (Equiv.ofBijective f hb) ^ Fintype.card (Equiv.Perm G) = 1 := pow_card_eq_one
  funext x
  rw [show f = ⇑(Equiv.ofBijective f hb) from he.symm, Equiv.Perm.iterate_eq_pow, this]
  rfl

/-- **The glue.** On a finite magma whose translations are all injective, a `QTerm` names an
honest defining term: the divisions are iterated translations at an exponent read off the carrier.
So to term-define `L` it suffices that the target hold of the `QTerm` in any structure equipped
with two-sided divisions. -/
theorem termDefinableOnMagma_of_qterm [Finite G] {β : Type} {L : Law.MagmaLaw β}
    (M : Magma G) (q : QTerm)
    (hr : ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hl : ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ rd ld : G → G → G,
      (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
      (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
      @satisfies _ G ⟨q.eval M.op rd ld⟩ L) :
    TermDefinableOnMagma L M := by
  obtain ⟨N, hN⟩ := exists_uniform_period G
  let rd : G → G → G := fun a b ↦ (fun u ↦ M.op u b)^[N] a
  let ld : G → G → G := fun a b ↦ (fun u ↦ M.op a u)^[N] b
  -- `f^[N] (f a) = a` is the iterate identity read as it stands; `f (f^[N] a) = a` is the same
  -- identity read from the other end, which is `Function.iterate_succ_apply'`
  have hrs (a b : G) : M.op (rd a b) b = a := by
    have h := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
    rwa [Function.iterate_succ_apply'] at h
  have hri (a b : G) : rd (M.op a b) b = a := congrFun (hN (fun u ↦ M.op u b) (hr b)) a
  have hls (a b : G) : M.op a (ld a b) = b := by
    have h := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
    rwa [Function.iterate_succ_apply'] at h
  have hli (a b : G) : ld a (M.op a b) = b := congrFun (hN (fun u ↦ M.op a u) (hl a)) b
  -- the compiled term denotes exactly the operation the `QTerm` evaluates to
  have key : ∀ p : QTerm, ∀ x y : G,
      bsem M (p.toBTerm (G := G) N) x y = p.eval M.op rd ld x y := by
    intro p
    induction p with
    | var i =>
      intro x y
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    | op a b iha ihb =>
      intro x y
      rw [show bsem M ((QTerm.op a b).toBTerm (G := G) N) x y
        = M.op (bsem M (a.toBTerm N) x y) (bsem M (b.toBTerm N) x y) from rfl, iha, ihb]
      rfl
    | rdv a b iha ihb =>
      intro x y
      rw [show (QTerm.rdv a b).toBTerm (G := G) N
        = riter (a.toBTerm N) (b.toBTerm N) N from rfl, bsem_riter, iha, ihb]
      rfl
    | ldv a b iha ihb =>
      intro x y
      rw [show (QTerm.ldv a b).toBTerm (G := G) N
        = liter (a.toBTerm N) (b.toBTerm N) N from rfl, bsem_liter, iha, ihb]
      rfl
  refine ⟨⟨q.eval M.op rd ld⟩, hsat rd ld hrs hri hls hli, ⟨q.toBTerm (G := G) N, ?_⟩⟩
  funext w
  have hw : ![w 0, w 1] = w := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  show q.eval M.op rd ld (w 0) (w 1) = _
  rw [← key q (w 0) (w 1)]
  show @Term.realize _ G M.FOStructure₀ _ ![w 0, w 1] (q.toBTerm (G := G) N) = _
  rw [hw]

/-- The `TermDefinableFromFin` wrapper: the `QTerm` is uniform, only the exponent hidden inside
`toBTerm` is chosen after the magma. -/
theorem termDefinableFromFin_of_qterm {β : Type} {L L' : Law.MagmaLaw β} (q : QTerm)
    (hr : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ b : G, Function.Injective fun a ↦ M.op a b)
    (hl : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ a : G, Function.Injective fun b ↦ M.op a b)
    (hsat : ∀ (G : Type) [Finite G] (M : Magma G), satisfies G L' →
      ∀ rd ld : G → G → G,
        (∀ a b, M.op (rd a b) b = a) → (∀ a b, rd (M.op a b) b = a) →
        (∀ a b, M.op a (ld a b) = b) → (∀ a b, ld a (M.op a b) = b) →
        @satisfies _ G ⟨q.eval M.op rd ld⟩ L) :
    TermDefinableFromFin L L' :=
  fun {G} _ M hM ↦
    termDefinableOnMagma_of_qterm M q (hr G M hM) (hl G M hM) (hsat G M hM)

end Law.MagmaLaw
