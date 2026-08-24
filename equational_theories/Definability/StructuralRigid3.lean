import equational_theories.Definability.Structural
import equational_theories.DecideBangNative

/-!
# Structural certificates from rigidity on `Fin 3`

`Definability/Structural.lean` refutes structurality from a magma with *no* symmetry on `Fin 2`,
and `Definability/StructuralFin3.lean` does the two middle automorphism groups on `Fin 3`. This
file is the last of the four classes at order `3`: the trivial group again.

It is separated out because it is the only one whose family cannot be cut down. The three others
are pinned by a classification lemma — a magma admitting the cyclic shift is determined by its
first row, one admitting the reflection by four entries — whereas "no automorphism at all" is a
condition on the whole table, so the family has to be indexed by all `3 ^ 9 = 19683` of them, of
which `19422` are rigid.

The argument is one-sided in the opposite way to the exact-`Aut` files. There, both directions of
the structural definability did work; here the forward one says nothing, because every
automorphism group contains the trivial one, and the whole certificate rests on the backward
definability carrying `Aut(M') ≤ Aut(M) = 1`.

## Why the family is spelled out twice

`19683` tables is far past what the kernel will walk, so `Definability/Certs/Rigid3*.lean` is
checked by `nativeDecideFin!`, which hands the family to Lean's *interpreter*. That makes the
constant factor of a single table lookup the thing that decides whether the certificate can be
landed at all, and the two obvious ways to write the family down are both too slow: `![![a, b, c],
…]` allocates a `Matrix.vecCons` cell per lookup, and `⇑(Equiv.swap 0 1)` goes through
`Equiv.instFunLike` and a `DecidableEq` test. Measured on a twelve-equation certificate, the
`Matrix`-and-`Equiv` version of this file took `191` seconds where the version below takes a small
fraction of that.

So the data is given twice. `tab3` and `perm3` are plain pattern matches, and `hasSym3` is a
`Bool`, and those are what `Magma.rigid3` computes with; `perms3` is the same five permutations as
`Equiv.Perm (Fin 3)`, which is what `Magma.IsEndo` and hence `Magma.IsEndo.of_definable` needs.
`perms3_eq` and `hasSym3_iff` are the bridge, and they are the only places the two meet.

`Definability/Certs/Rigid3*.lean` records the rectangle.
-/

open Law Law.MagmaLaw

namespace Magma

/-! ### The family -/

/-- The five non-identity permutations of `Fin 3`: a magma on `Fin 3` is rigid exactly when none
of them is an automorphism of it. -/
def perms3 : Fin 5 → Equiv.Perm (Fin 3)
  | 0 => Equiv.swap 0 1
  | 1 => Equiv.swap 0 2
  | 2 => Equiv.swap 1 2
  | 3 => Equiv.addRight 1
  | 4 => Equiv.addRight 2

/-- `Magma.perms3` again, as bare functions. -/
def perm3 : Fin 5 → Fin 3 → Fin 3
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => 2
  | 1, 0 => 2 | 1, 1 => 1 | 1, 2 => 0
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 1
  | 3, 0 => 1 | 3, 1 => 2 | 3, 2 => 0
  | 4, 0 => 2 | 4, 1 => 0 | 4, 2 => 1

theorem perms3_eq (j : Fin 5) : ⇑(perms3 j) = perm3 j := by
  funext x; revert j x; decide

/-- A binary operation on `Fin 3` from its nine entries, read in reading order. -/
def tab3 (a b c d e f g h i : Fin 3) : Fin 3 → Fin 3 → Fin 3
  | 0, 0 => a | 0, 1 => b | 0, 2 => c
  | 1, 0 => d | 1, 1 => e | 1, 2 => f
  | 2, 0 => g | 2, 1 => h | 2, 2 => i

/-- `∀ x : Fin 3, f x`, unrolled. -/
def allFin3 (f : Fin 3 → Bool) : Bool := f 0 && f 1 && f 2

theorem allFin3_iff (f : Fin 3 → Bool) : allFin3 f = true ↔ ∀ x, f x = true := by
  simp only [allFin3, Bool.and_eq_true]
  exact ⟨fun ⟨⟨h₀, h₁⟩, h₂⟩ x ↦ by fin_cases x <;> assumption, fun h ↦ ⟨⟨h 0, h 1⟩, h 2⟩⟩

/-- Whether `p` is an endomorphism of the operation `t`. -/
def isEndo3 (t : Fin 3 → Fin 3 → Fin 3) (p : Fin 3 → Fin 3) : Bool :=
  allFin3 fun x ↦ allFin3 fun y ↦ p (t x y) == t (p x) (p y)

theorem isEndo3_iff (t : Fin 3 → Fin 3 → Fin 3) (p : Fin 3 → Fin 3) :
    isEndo3 t p = true ↔ ∀ x y, p (t x y) = t (p x) (p y) := by
  simp only [isEndo3, allFin3_iff, beq_iff_eq]

/-- Whether the operation `t` has any automorphism other than the identity. -/
def hasSym3 (t : Fin 3 → Fin 3 → Fin 3) : Bool :=
  isEndo3 t (perm3 0) || isEndo3 t (perm3 1) || isEndo3 t (perm3 2) || isEndo3 t (perm3 3) ||
    isEndo3 t (perm3 4)

theorem hasSym3_iff (t : Fin 3 → Fin 3 → Fin 3) :
    hasSym3 t = true ↔ ∃ j, (Magma.mk t).IsEndo (perm3 j) := by
  simp only [hasSym3, Bool.or_eq_true, isEndo3_iff]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩]
  · rintro ⟨j, h⟩
    fin_cases j
    exacts [Or.inl (Or.inl (Or.inl (Or.inl h))), Or.inl (Or.inl (Or.inl (Or.inr h))),
      Or.inl (Or.inl (Or.inr h)), Or.inl (Or.inr h), Or.inr h]

/-- The `19422` rigid magmas on `Fin 3`, as a family indexed by all `19683` tables: the `261`
non-rigid ones are redirected onto the magma with `0 ◇ 2 = 1` and every other entry `0`, which is
rigid. -/
@[implicit_reducible]
def rigid3 (a b c d e f g h i : Fin 3) : Magma (Fin 3) :=
  if hasSym3 (tab3 a b c d e f g h i) then Magma.mk (tab3 0 0 1 0 0 0 0 0 0)
  else Magma.mk (tab3 a b c d e f g h i)

/-! ### The certificate -/

theorem rigid3_not_isEndo (a b c d e f g h i : Fin 3) (j : Fin 5) :
    ¬ (rigid3 a b c d e f g h i).IsEndo ⇑(perms3 j) := by
  simp only [perms3_eq]
  revert a b c d e f g h i j
  native_decide

/-- A rigid magma on `Fin 3` *is* the member of `Magma.rigid3` named by its nine entries. -/
theorem rigid3_eq_self {M : Magma (Fin 3)} (h : ∀ j, ¬ M.IsEndo ⇑(perms3 j)) :
    rigid3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1) (M.op 1 2)
      (M.op 2 0) (M.op 2 1) (M.op 2 2) = M := by
  have key : Magma.mk (tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1) (M.op 1 2)
      (M.op 2 0) (M.op 2 1) (M.op 2 2)) = M := by
    obtain ⟨op⟩ := M
    refine congrArg Magma.mk (funext fun x ↦ funext fun y ↦ ?_)
    fin_cases x <;> fin_cases y <;> rfl
  have hg : hasSym3 (tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1) (M.op 1 2)
      (M.op 2 0) (M.op 2 1) (M.op 2 2)) = false := by
    rw [Bool.eq_false_iff, ne_eq, hasSym3_iff]
    rintro ⟨j, hj⟩
    rw [key] at hj
    exact h j (by rwa [perms3_eq])
  simp only [rigid3, key, hg, Bool.false_eq_true, if_false]

end Magma

namespace Law.MagmaLaw

/-- **Rigid certificate on `Fin 3`.** If `L'` has a rigid model on `Fin 3` and no rigid magma on
`Fin 3` satisfies `L`, then `L` is not structural from `L'`, not even over finite carriers. -/
theorem not_structuralFromFin_of_rigid3 {L L' : Law.NatMagmaLaw} {a b c d e f g h i : Fin 3}
    (hsrc : @satisfies _ (Fin 3) (Magma.rigid3 a b c d e f g h i) L')
    (htgt : ∀ a b c d e f g h i : Fin 3,
      ¬ @satisfies _ (Fin 3) (Magma.rigid3 a b c d e f g h i) L) :
    ¬ L.StructuralFromFin L' := by
  intro hst
  obtain ⟨M', hM', -, hback⟩ := hst (Magma.rigid3 a b c d e f g h i) hsrc
  refine htgt (M'.op 0 0) (M'.op 0 1) (M'.op 0 2) (M'.op 1 0) (M'.op 1 1) (M'.op 1 2)
    (M'.op 2 0) (M'.op 2 1) (M'.op 2 2) ?_
  rw [Magma.rigid3_eq_self fun j hj ↦ Magma.rigid3_not_isEndo a b c d e f g h i j
    (hj.of_definable hback)]
  exact hM'

end Law.MagmaLaw
