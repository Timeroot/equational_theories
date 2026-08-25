import equational_theories.Definability.Structural
import equational_theories.Definability.Transport
import equational_theories.DecideBangNative

/-!
# Machinery for exact-automorphism families on `Fin n`

`Definability/Structural.lean` turns structurality into a statement about automorphism groups: a
structural companion `M'` of `M` has `Aut(M') = Aut(M)` on the nose. So each conjugacy class of
subgroup `H ≤ Sₙ` gives a rectangle of refutations — the laws with a model on `Fin n` whose
automorphism group is *exactly* `H` cannot be structural over the laws with none.

`Definability/StructuralFin3.lean`, `StructuralRigid3.lean` and `StructuralFin4.lean` each spend
one such class, and each pays for its own classification lemma. This file collects what all of
them have in common, so that a new class is pure data:

* **which permutations to demand and which to forbid.** `Aut(M) = H` is not a condition on single
  permutations, `Aut(M)` being a group: it is `H ≤ Aut(M)` together with `K ⊄ Aut(M)` for every
  subgroup `K ⊋ H`. But a group containing `K` contains any chosen element of `K \ H`, so a set of
  permutations meeting every such `K` outside `H` does the job, and it is usually tiny — two for
  `C₃ ≤ S₄`, one for the dihedral group. `Magma.isExact` is the resulting test.
* **how to write that test down so Lean's interpreter can afford it.** The family is walked once
  per candidate target law and the guard sits on the hot path, so the quantifiers are unrolled
  rather than left to `Fintype`, exactly as `Magma.isEndo3` does in `StructuralRigid3.lean`.
* **the classification**, which `Definability/Transport.lean` already gives generically:
  `Magma.op_eq_transport` says an operation invariant under `H` is one value per orbit of `H` on
  the `n²` cells, transported around, so the family is indexed by `n ^ m` tuples with `m` the
  number of orbits and the non-invariant tuples are redirected by `Magma.famOf`.

`Definability/ExactAut4.lean` is the generated instance of all this for the remaining classes on
`Fin 4`.
-/

universe u

namespace Magma

variable {G : Type u} {n kE kX : ℕ}

/-- Structure eta as a rewrite rule: a magma is its own operation, wrapped. -/
@[simp] theorem mk_op (M : Magma G) : Magma.mk M.op = M := rfl

/-! ### Deciding endomorphism tests quickly -/

/-- `∀ x : Fin n, f x`, unrolled. The `Fintype` instance for `∀ x : Fin n, _` folds over
`Finset.univ` and allocates a list per call; on the hot path of a family scan that constant factor
is most of the cost. -/
def allFin : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f 0 && allFin n fun i ↦ f i.succ

theorem allFin_iff : ∀ {n : ℕ} {f : Fin n → Bool}, allFin n f = true ↔ ∀ x, f x = true
  | 0, _ => by simp [allFin]
  | n + 1, f => by
    simp only [allFin, Bool.and_eq_true, allFin_iff]
    refine ⟨fun ⟨h₀, hs⟩ x ↦ ?_, fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩⟩
    cases x using Fin.cases with
    | zero => exact h₀
    | succ i => exact hs i

/-- Whether `p` is an endomorphism of the operation `t`, with both quantifiers unrolled. -/
def isEndoFin (t : Fin n → Fin n → Fin n) (p : Fin n → Fin n) : Bool :=
  allFin n fun x ↦ allFin n fun y ↦ p (t x y) == t (p x) (p y)

theorem isEndoFin_iff {t : Fin n → Fin n → Fin n} {p : Fin n → Fin n} :
    isEndoFin t p = true ↔ (Magma.mk t).IsEndo p := by
  simp only [isEndoFin, allFin_iff, beq_iff_eq]
  rfl

theorem isEndoFin_eq_false_iff {t : Fin n → Fin n → Fin n} {p : Fin n → Fin n} :
    isEndoFin t p = false ↔ ¬ (Magma.mk t).IsEndo p := by
  rw [← isEndoFin_iff, Bool.not_eq_true]

/-- Whether the operation `t` admits every `pE i` and no `pX i` — that is, whether its
automorphism group is exactly the group that data describes. -/
def isExact (t : Fin n → Fin n → Fin n) (pE : Fin kE → Fin n → Fin n)
    (pX : Fin kX → Fin n → Fin n) : Bool :=
  allFin kE (fun i ↦ isEndoFin t (pE i)) && allFin kX fun i ↦ !isEndoFin t (pX i)

theorem isExact_iff {t : Fin n → Fin n → Fin n} {pE : Fin kE → Fin n → Fin n}
    {pX : Fin kX → Fin n → Fin n} :
    isExact t pE pX = true ↔
      (∀ i, (Magma.mk t).IsEndo (pE i)) ∧ ∀ i, ¬ (Magma.mk t).IsEndo (pX i) := by
  simp only [isExact, Bool.and_eq_true, allFin_iff, isEndoFin_iff, Bool.not_eq_true',
    isEndoFin_eq_false_iff]

/-! ### Assembling a family -/

/-- The member of an exact-`Aut` family named by a table: the table itself when its automorphism
group really is the intended one, and a fixed member `d` when it is not. Indexing by all `n ^ m`
transport tuples and redirecting the bad ones is what keeps the index type a product of `Fin`s,
which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def famOf (t : Fin n → Fin n → Fin n) (pE : Fin kE → Fin n → Fin n)
    (pX : Fin kX → Fin n → Fin n) (d : Fin n → Fin n → Fin n) : Magma (Fin n) :=
  if isExact t pE pX then Magma.mk t else Magma.mk d

theorem famOf_eq {t : Fin n → Fin n → Fin n} {pE : Fin kE → Fin n → Fin n}
    {pX : Fin kX → Fin n → Fin n} {d : Fin n → Fin n → Fin n} (h : isExact t pE pX = true) :
    famOf t pE pX d = Magma.mk t := if_pos h

/-- **Which values an orbit may take.** A permutation fixing both coordinates of the pair `(a, b)`
fixes `M.op a b` too, so the value at an orbit representative lies in the common fixed-point set of
that pair's stabilizer -- and that is usually a proper subset of `Fin n`. Indexing the orbit by
`Fin t` through such a `val` instead of by `Fin n` is what makes the family scanned the invariant
one rather than the whole tuple space: for the three-cycle on `Fin 4` that is `1024` members
instead of `4096`, and for `S₃` on `Fin 4` it is `32` instead of `1024`.

`idx` picks the stabilizing permutations out of the group `E`; both `hab` and `hval` are `decide`s
on a concrete carrier. -/
theorem exists_val_of_isEndo {kE s t : ℕ} {M : Magma (Fin n)} {E : Fin kE → Fin n → Fin n}
    {idx : Fin s → Fin kE} {a b : Fin n} {val : Fin t → Fin n}
    (hE : ∀ j, M.IsEndo (E j)) (hab : ∀ j, E (idx j) a = a ∧ E (idx j) b = b)
    (hval : ∀ x : Fin n, (∀ j, E (idx j) x = x) → ∃ y, val y = x) :
    ∃ y, val y = M.op a b :=
  hval _ fun j ↦ by rw [hE (idx j) a b, (hab j).1, (hab j).2]

/-- A permutation of `Fin n` from a function, its inverse and one `decide`. `Magma.IsEndo` takes a
bare function but `Magma.IsEndo.of_definable` needs an `Equiv`, and going through `Equiv.swap` or
`Equiv.addRight` would put an `Equiv.instFunLike` and a `DecidableEq` test on the hot path; here
the coercion is the bare function back again, by `rfl`. -/
def permOf (f g : Fin n → Fin n) (h : ∀ x, g (f x) = x ∧ f (g x) = x) : Equiv.Perm (Fin n) :=
  ⟨f, g, fun x ↦ (h x).1, fun x ↦ (h x).2⟩

@[simp] theorem coe_permOf {f g : Fin n → Fin n} {h} : ⇑(permOf f g h) = f := rfl

end Magma
