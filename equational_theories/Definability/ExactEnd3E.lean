import equational_theories.Definability.ExactEnd3

/-!
# The exact-endomorphism class `E` on `Fin 3`

One class of `Definability/ExactEnd3.lean`, in its own module so that the classes elaborate in
parallel; see that file for what the pieces mean.
-/

open Law Law.MagmaLaw

namespace Magma

/-- The `3` self-maps of `Fin 3` that must be endomorphisms: `3_012`, `3_120`, `3_201`. -/
def endE3E : Fin 3 → Fin 3 → Fin 3
  | 0 => Magma.m3_012
  | 1 => Magma.m3_120
  | 2 => Magma.m3_201

/-- The other `24`, which must not be. `End` of a magma is a submonoid of all `27`, so demanding the
first list and forbidding this one says `End(M)` is exactly the first list. -/
def endX3E : Fin 24 → Fin 3 → Fin 3
  | 0 => Magma.m3_000
  | 1 => Magma.m3_001
  | 2 => Magma.m3_002
  | 3 => Magma.m3_010
  | 4 => Magma.m3_011
  | 5 => Magma.m3_020
  | 6 => Magma.m3_021
  | 7 => Magma.m3_022
  | 8 => Magma.m3_100
  | 9 => Magma.m3_101
  | 10 => Magma.m3_102
  | 11 => Magma.m3_110
  | 12 => Magma.m3_111
  | 13 => Magma.m3_112
  | 14 => Magma.m3_121
  | 15 => Magma.m3_122
  | 16 => Magma.m3_200
  | 17 => Magma.m3_202
  | 18 => Magma.m3_210
  | 19 => Magma.m3_211
  | 20 => Magma.m3_212
  | 21 => Magma.m3_220
  | 22 => Magma.m3_221
  | _ => Magma.m3_222

/-- The `18` operations on `Fin 3` whose endomorphism monoid is exactly `endE3E`, listed under one
index. Listing them rather than guarding a nine-argument family keeps the exactness test off the hot
path of a scan; see the module docstring of `Definability.ExactEnd3`. -/
def mem3E : Fin 18 → Fin 3 → Fin 3 → Fin 3
  | 0 => tab3 1 0 0 1 2 1 2 2 0
  | 1 => tab3 1 0 1 2 2 1 2 0 0
  | 2 => tab3 1 0 2 0 2 1 2 1 0
  | 3 => tab3 1 1 0 1 2 2 0 2 0
  | 4 => tab3 1 1 1 2 2 2 0 0 0
  | 5 => tab3 1 1 2 0 2 2 0 1 0
  | 6 => tab3 1 2 0 1 2 0 1 2 0
  | 7 => tab3 1 2 1 2 2 0 1 0 0
  | 8 => tab3 1 2 2 0 2 0 1 1 0
  | 9 => tab3 2 0 0 1 0 1 2 2 1
  | 10 => tab3 2 0 1 2 0 1 2 0 1
  | 11 => tab3 2 0 2 0 0 1 2 1 1
  | 12 => tab3 2 1 0 1 0 2 0 2 1
  | 13 => tab3 2 1 1 2 0 2 0 0 1
  | 14 => tab3 2 1 2 0 0 2 0 1 1
  | 15 => tab3 2 2 0 1 0 0 1 2 1
  | 16 => tab3 2 2 1 2 0 0 1 0 1
  | _ => tab3 2 2 2 0 0 0 1 1 1

/-- The same as a family of magmas, which is what `FamilyRefutes` scans. -/
@[implicit_reducible]
def end3E (i : Fin 18) : Magma (Fin 3) := Magma.mk (mem3E i)

theorem end3E_isEndo (i : Fin 18) (j : Fin 3) : (end3E i).IsEndo (endE3E j) := by
  revert i j; decide

theorem end3E_not_isEndo (i : Fin 18) (j : Fin 24) : ¬ (end3E i).IsEndo (endX3E j) := by
  revert i j; decide

/-- Every operation on `Fin 3` with this endomorphism monoid is one of the `18` listed. All `19,683`
tables are enumerated: there are few enough that searching the member list for each is cheaper than
tabulating the answer. -/
theorem mem_of_isExact3E (a b c d e f g h i : Fin 3)
    (hx : Magma.isExact (tab3 a b c d e f g h i) endE3E endX3E = true) :
    ∃ j, mem3E j = tab3 a b c d e f g h i := by
  revert hx; revert a b c d e f g h i; native_decide

/-- A magma on `Fin 3` admitting every map of `endE3E` and none of `endX3E` *is* a member of
`Magma.end3E`. -/
theorem exists_end3E {M : Magma (Fin 3)} (hE : ∀ j, M.IsEndo (endE3E j))
    (hX : ∀ j, ¬ M.IsEndo (endX3E j)) : ∃ j, end3E j = M := by
  have key : tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1) (M.op 1 2)
      (M.op 2 0) (M.op 2 1) (M.op 2 2) = M.op := op_eq_tab3 M
  have hok : Magma.isExact (tab3 (M.op 0 0) (M.op 0 1) (M.op 0 2) (M.op 1 0) (M.op 1 1)
      (M.op 1 2) (M.op 2 0) (M.op 2 1) (M.op 2 2)) endE3E endX3E = true := by
    rw [key, Magma.isExact_iff]; exact ⟨hE, hX⟩
  obtain ⟨j, hj⟩ := mem_of_isExact3E _ _ _ _ _ _ _ _ _ hok
  exact ⟨j, (congrArg Magma.mk (hj.trans key)).trans (Magma.mk_op M)⟩

end Magma

namespace Law.MagmaLaw

/-- **Exact-`End` certificate on `Fin 3`.** If `L'` has a model on `Fin 3` whose endomorphism
monoid is exactly the order-`3` monoid of `Magma.endE3E`, and no such magma satisfies `L`, then `L`
is not term-structural from `L'`, not even over finite carriers. -/
theorem not_termStructuralFromFin_of_end3E {L L' : Law.NatMagmaLaw} {i : Fin 18}
    (hsrc : @satisfies _ (Fin 3) (Magma.end3E i) L')
    (htgt : ∀ j, ¬ @satisfies _ (Fin 3) (Magma.end3E j) L) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h (Magma.end3E i) hsrc
  obtain ⟨j, hM⟩ := Magma.exists_end3E
    (fun k ↦ (Magma.end3E_isEndo i k).of_termDefinable hfwd)
    (fun k hn ↦ Magma.end3E_not_isEndo i k (hn.of_termDefinable hback))
  exact htgt j (by rw [hM]; exact hM')

end Law.MagmaLaw
