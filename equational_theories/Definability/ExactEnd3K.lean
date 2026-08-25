import equational_theories.Definability.ExactEnd3

/-!
# The exact-endomorphism class `K` on `Fin 3`

One class of `Definability/ExactEnd3.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

open Law Law.MagmaLaw

namespace Magma

/-- The `3` self-maps of `Fin 3` that must be endomorphisms: `3_011`, `3_012`, `3_100`. -/
def endE3K : Fin 3 → Fin 3 → Fin 3
  | 0 => Magma.m3_011
  | 1 => Magma.m3_012
  | 2 => Magma.m3_100

/-- The other `24`, which must not be. `End` of a magma is a submonoid of all `27`, so demanding the
first list and forbidding this one says `End(M)` is exactly the first list. -/
def endX3K : Fin 24 → Fin 3 → Fin 3
  | 0 => Magma.m3_000
  | 1 => Magma.m3_001
  | 2 => Magma.m3_002
  | 3 => Magma.m3_010
  | 4 => Magma.m3_020
  | 5 => Magma.m3_021
  | 6 => Magma.m3_022
  | 7 => Magma.m3_101
  | 8 => Magma.m3_102
  | 9 => Magma.m3_110
  | 10 => Magma.m3_111
  | 11 => Magma.m3_112
  | 12 => Magma.m3_120
  | 13 => Magma.m3_121
  | 14 => Magma.m3_122
  | 15 => Magma.m3_200
  | 16 => Magma.m3_201
  | 17 => Magma.m3_202
  | 18 => Magma.m3_210
  | 19 => Magma.m3_211
  | 20 => Magma.m3_212
  | 21 => Magma.m3_220
  | 22 => Magma.m3_221
  | _ => Magma.m3_222

/-- The `4` operations on `Fin 3` whose endomorphism monoid is exactly `endE3K`, listed under one
index. Listing them rather than guarding a nine-argument family keeps the exactness test off the hot
path of a scan; see the module docstring of `Definability.ExactEnd3`. -/
def mem3K : Fin 4 → Fin 3 → Fin 3 → Fin 3
  | 0 => tab3 1 0 0 1 0 0 1 0 0
  | 1 => tab3 1 0 0 1 0 0 2 0 0
  | 2 => tab3 1 1 1 0 0 0 0 0 0
  | 3 => tab3 1 1 2 0 0 0 0 0 0

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end3K (i : Fin 4) : Magma (Fin 3) := Magma.mk (mem3K i)

theorem end3K_isEndo (i : Fin 4) (j : Fin 3) : (end3K i).IsEndo (endE3K j) := by
  revert i j; decide

theorem end3K_not_isEndo (i : Fin 4) (j : Fin 24) : ¬ (end3K i).IsEndo (endX3K j) := by
  revert i j; decide

/-- Every operation on `Fin 3` with this endomorphism monoid is one of the `4` listed. All `19,683`
tables are enumerated: there are few enough that searching the member list for each is cheaper than
tabulating the answer. -/
theorem mem_of_isExact3K (a b c d e f g h i : Fin 3)
    (hx : Magma.isExact (tab3 a b c d e f g h i) endE3K endX3K = true) :
    ∃ j, mem3K j = tab3 a b c d e f g h i := by
  revert hx; revert a b c d e f g h i; native_decide

/-- A magma on `Fin 3` admitting every map of `endE3K` and none of `endX3K` *is* a member of
`Magma.end3K`. -/
theorem exists_end3K {M : Magma (Fin 3)} (hE : ∀ j, M.IsEndo (endE3K j))
    (hX : ∀ j, ¬ M.IsEndo (endX3K j)) : ∃ j, end3K j = M := by
  have key : tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1) (M.op 1 2)
      (M.op 2 0) (M.op 2 1) (M.op 2 2) = M.op := op_eq_tab3 M
  have hok : Magma.isExact (tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1)
      (M.op 1 2) (M.op 2 0) (M.op 2 1) (M.op 2 2)) endE3K endX3K = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨j, hj⟩ := mem_of_isExact3K _ _ _ _ _ _ _ _ _ hok
  exact ⟨j, (congrArg Magma.mk (hj.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 3`.** If `L'` has a model on `Fin 3` whose endomorphism
monoid is exactly the order-`3` monoid of `Magma.endE3K`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end3K {L L' : Law.NatMagmaLaw} {i : Fin 4}
    (hsrc : @satisfies _ (Fin 3) (Magma.end3K i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 3) (Magma.end3K j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end3K i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end3K
    (fun k ↦ (Magma.end3K_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end3K_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
