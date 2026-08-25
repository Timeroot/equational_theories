import equational_theories.Definability.ExactEnd3

/-!
# The exact-endomorphism class `S` on `Fin 3`

One class of `Definability/ExactEnd3.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

open Law Law.MagmaLaw

namespace Magma

/-- The `5` self-maps of `Fin 3` that must be endomorphisms: `3_000`, `3_011`, `3_012`, `3_021`,
`3_022`. -/
def endE3S : Fin 5 → Fin 3 → Fin 3
  | 0 => Magma.m3_000
  | 1 => Magma.m3_011
  | 2 => Magma.m3_012
  | 3 => Magma.m3_021
  | 4 => Magma.m3_022

/-- The other `22`, which must not be. `End` of a magma is a submonoid of all `27`, so demanding the
first list and forbidding this one says `End(M)` is exactly the first list. -/
def endX3S : Fin 22 → Fin 3 → Fin 3
  | 0 => Magma.m3_001
  | 1 => Magma.m3_002
  | 2 => Magma.m3_010
  | 3 => Magma.m3_020
  | 4 => Magma.m3_100
  | 5 => Magma.m3_101
  | 6 => Magma.m3_102
  | 7 => Magma.m3_110
  | 8 => Magma.m3_111
  | 9 => Magma.m3_112
  | 10 => Magma.m3_120
  | 11 => Magma.m3_121
  | 12 => Magma.m3_122
  | 13 => Magma.m3_200
  | 14 => Magma.m3_201
  | 15 => Magma.m3_202
  | 16 => Magma.m3_210
  | 17 => Magma.m3_211
  | 18 => Magma.m3_212
  | 19 => Magma.m3_220
  | 20 => Magma.m3_221
  | _ => Magma.m3_222

/-- The `3` operations on `Fin 3` whose endomorphism monoid is exactly `endE3S`, listed under one
index. Listing them rather than guarding a nine-argument family keeps the exactness test off the hot
path of a scan; see the module docstring of `Definability.ExactEnd3`. -/
def mem3S : Fin 3 → Fin 3 → Fin 3 → Fin 3
  | 0 => tab3 0 0 0 1 0 0 2 0 0
  | 1 => tab3 0 1 2 0 0 0 0 0 0
  | 2 => tab3 0 1 2 1 0 0 2 0 0

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end3S (i : Fin 3) : Magma (Fin 3) := Magma.mk (mem3S i)

theorem end3S_isEndo (i : Fin 3) (j : Fin 5) : (end3S i).IsEndo (endE3S j) := by
  revert i j; decide

theorem end3S_not_isEndo (i : Fin 3) (j : Fin 22) : ¬ (end3S i).IsEndo (endX3S j) := by
  revert i j; decide

/-- Every operation on `Fin 3` with this endomorphism monoid is one of the `3` listed. All `19,683`
tables are enumerated: there are few enough that searching the member list for each is cheaper than
tabulating the answer. -/
theorem mem_of_isExact3S (a b c d e f g h i : Fin 3)
    (hx : Magma.isExact (tab3 a b c d e f g h i) endE3S endX3S = true) :
    ∃ j, mem3S j = tab3 a b c d e f g h i := by
  revert hx; revert a b c d e f g h i; native_decide

/-- A magma on `Fin 3` admitting every map of `endE3S` and none of `endX3S` *is* a member of
`Magma.end3S`. -/
theorem exists_end3S {M : Magma (Fin 3)} (hE : ∀ j, M.IsEndo (endE3S j))
    (hX : ∀ j, ¬ M.IsEndo (endX3S j)) : ∃ j, end3S j = M := by
  have key : tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1) (M.op 1 2)
      (M.op 2 0) (M.op 2 1) (M.op 2 2) = M.op := op_eq_tab3 M
  have hok : Magma.isExact (tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1)
      (M.op 1 2) (M.op 2 0) (M.op 2 1) (M.op 2 2)) endE3S endX3S = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨j, hj⟩ := mem_of_isExact3S _ _ _ _ _ _ _ _ _ hok
  exact ⟨j, (congrArg Magma.mk (hj.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 3`.** If `L'` has a model on `Fin 3` whose endomorphism
monoid is exactly the order-`5` monoid of `Magma.endE3S`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end3S {L L' : Law.NatMagmaLaw} {i : Fin 3}
    (hsrc : @satisfies _ (Fin 3) (Magma.end3S i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 3) (Magma.end3S j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end3S i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end3S
    (fun k ↦ (Magma.end3S_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end3S_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
