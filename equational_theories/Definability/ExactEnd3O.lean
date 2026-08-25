import equational_theories.Definability.ExactEnd3

/-!
# The exact-endomorphism class `O` on `Fin 3`

One class of `Definability/ExactEnd3.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

open Law Law.MagmaLaw

namespace Magma

/-- The `5` self-maps of `Fin 3` that must be endomorphisms: `3_000`, `3_002`, `3_010`, `3_012`,
`3_222`. -/
def endE3O : Fin 5 → Fin 3 → Fin 3
  | 0 => Magma.m3_000
  | 1 => Magma.m3_002
  | 2 => Magma.m3_010
  | 3 => Magma.m3_012
  | 4 => Magma.m3_222

/-- The other `22`, which must not be. `End` of a magma is a submonoid of all `27`, so demanding the
first list and forbidding this one says `End(M)` is exactly the first list. -/
def endX3O : Fin 22 → Fin 3 → Fin 3
  | 0 => Magma.m3_001
  | 1 => Magma.m3_011
  | 2 => Magma.m3_020
  | 3 => Magma.m3_021
  | 4 => Magma.m3_022
  | 5 => Magma.m3_100
  | 6 => Magma.m3_101
  | 7 => Magma.m3_102
  | 8 => Magma.m3_110
  | 9 => Magma.m3_111
  | 10 => Magma.m3_112
  | 11 => Magma.m3_120
  | 12 => Magma.m3_121
  | 13 => Magma.m3_122
  | 14 => Magma.m3_200
  | 15 => Magma.m3_201
  | 16 => Magma.m3_202
  | 17 => Magma.m3_210
  | 18 => Magma.m3_211
  | 19 => Magma.m3_212
  | 20 => Magma.m3_220
  | _ => Magma.m3_221

/-- The `5` operations on `Fin 3` whose endomorphism monoid is exactly `endE3O`, listed under one
index. Listing them rather than guarding a nine-argument family keeps the exactness test off the hot
path of a scan; see the module docstring of `Definability.ExactEnd3`. -/
def mem3O : Fin 5 → Fin 3 → Fin 3 → Fin 3
  | 0 => tab3 0 0 0 0 0 0 0 0 2
  | 1 => tab3 0 0 0 1 0 1 0 0 2
  | 2 => tab3 0 0 2 0 0 2 2 2 2
  | 3 => tab3 0 1 0 0 0 0 0 1 2
  | 4 => tab3 0 1 0 1 0 1 0 1 2

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end3O (i : Fin 5) : Magma (Fin 3) := Magma.mk (mem3O i)

theorem end3O_isEndo (i : Fin 5) (j : Fin 5) : (end3O i).IsEndo (endE3O j) := by
  revert i j; decide

theorem end3O_not_isEndo (i : Fin 5) (j : Fin 22) : ¬ (end3O i).IsEndo (endX3O j) := by
  revert i j; decide

/-- Every operation on `Fin 3` with this endomorphism monoid is one of the `5` listed. All `19,683`
tables are enumerated: there are few enough that searching the member list for each is cheaper than
tabulating the answer. -/
theorem mem_of_isExact3O (a b c d e f g h i : Fin 3)
    (hx : Magma.isExact (tab3 a b c d e f g h i) endE3O endX3O = true) :
    ∃ j, mem3O j = tab3 a b c d e f g h i := by
  revert hx; revert a b c d e f g h i; native_decide

/-- A magma on `Fin 3` admitting every map of `endE3O` and none of `endX3O` *is* a member of
`Magma.end3O`. -/
theorem exists_end3O {M : Magma (Fin 3)} (hE : ∀ j, M.IsEndo (endE3O j))
    (hX : ∀ j, ¬ M.IsEndo (endX3O j)) : ∃ j, end3O j = M := by
  have key : tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1) (M.op 1 2)
      (M.op 2 0) (M.op 2 1) (M.op 2 2) = M.op := op_eq_tab3 M
  have hok : Magma.isExact (tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1)
      (M.op 1 2) (M.op 2 0) (M.op 2 1) (M.op 2 2)) endE3O endX3O = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨j, hj⟩ := mem_of_isExact3O _ _ _ _ _ _ _ _ _ hok
  exact ⟨j, (congrArg Magma.mk (hj.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 3`.** If `L'` has a model on `Fin 3` whose endomorphism
monoid is exactly the order-`5` monoid of `Magma.endE3O`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end3O {L L' : Law.NatMagmaLaw} {i : Fin 5}
    (hsrc : @satisfies _ (Fin 3) (Magma.end3O i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 3) (Magma.end3O j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end3O i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end3O
    (fun k ↦ (Magma.end3O_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end3O_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
