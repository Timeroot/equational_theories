import equational_theories.Definability.LinearInt

/-!
# The cover of the integer certificate

The `184` non-definability facts that `(ℤ, x ◇ y = -x - y)` contributes to the open board: the two
targets of `Definability/LinearInt.lean` against each of the `92` equations the model satisfies.
Every one of them is new — no finite certificate in `Definability/` reaches any of these pairs, and
equations `3272` and `4091` are the two heaviest targets left, so this is the single largest block
of the board settled by one model.

The statements refute `TermDefinableFrom`, and only over all magmas: the witness is infinite, so
nothing here bears on the finite-magma variant, and a clone argument bounds terms rather than
formulas, so nothing here bears on `DefinableFrom` either.

This file is generated from the source list of `Definability/LinearInt.lean`; the projections pick
the relevant conjunct out of `Magma.negInt_satisfies_*` in the order the lists are written there.
-/

open Law.MagmaLaw

/-! ### Equation `3272` -/

theorem Equation3272_not_termDefinableFrom_Equation14 :
    ¬ Law3272.TermDefinableFrom Law14 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law14.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation29 :
    ¬ Law3272.TermDefinableFrom Law29 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law29.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation477 :
    ¬ Law3272.TermDefinableFrom Law477 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law477.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation489 :
    ¬ Law3272.TermDefinableFrom Law489 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law489.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation492 :
    ¬ Law3272.TermDefinableFrom Law492 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law492.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation522 :
    ¬ Law3272.TermDefinableFrom Law522 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law522.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation572 :
    ¬ Law3272.TermDefinableFrom Law572 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law572.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation680 :
    ¬ Law3272.TermDefinableFrom Law680 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law680.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation684 :
    ¬ Law3272.TermDefinableFrom Law684 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law684.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation692 :
    ¬ Law3272.TermDefinableFrom Law692 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law692.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation711 :
    ¬ Law3272.TermDefinableFrom Law711 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law711.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation725 :
    ¬ Law3272.TermDefinableFrom Law725 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law725.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation746 :
    ¬ Law3272.TermDefinableFrom Law746 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law746.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation759 :
    ¬ Law3272.TermDefinableFrom Law759 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law759.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1073 :
    ¬ Law3272.TermDefinableFrom Law1073 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1073.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1152 :
    ¬ Law3272.TermDefinableFrom Law1152 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1152.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1155 :
    ¬ Law3272.TermDefinableFrom Law1155 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1155.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1165 :
    ¬ Law3272.TermDefinableFrom Law1165 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1165.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1181 :
    ¬ Law3272.TermDefinableFrom Law1181 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1181.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1276 :
    ¬ Law3272.TermDefinableFrom Law1276 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1276.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1293 :
    ¬ Law3272.TermDefinableFrom Law1293 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1293.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1304 :
    ¬ Law3272.TermDefinableFrom Law1304 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1304.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1320 :
    ¬ Law3272.TermDefinableFrom Law1320 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1320.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1358 :
    ¬ Law3272.TermDefinableFrom Law1358 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1358.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1492 :
    ¬ Law3272.TermDefinableFrom Law1492 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1492.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1504 :
    ¬ Law3272.TermDefinableFrom Law1504 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1504.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1507 :
    ¬ Law3272.TermDefinableFrom Law1507 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1507.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1519 :
    ¬ Law3272.TermDefinableFrom Law1519 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1519.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1558 :
    ¬ Law3272.TermDefinableFrom Law1558 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1558.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1561 :
    ¬ Law3272.TermDefinableFrom Law1561 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1561.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1695 :
    ¬ Law3272.TermDefinableFrom Law1695 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1695.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1699 :
    ¬ Law3272.TermDefinableFrom Law1699 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1699.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1707 :
    ¬ Law3272.TermDefinableFrom Law1707 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1707.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1932 :
    ¬ Law3272.TermDefinableFrom Law1932 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1932.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1943 :
    ¬ Law3272.TermDefinableFrom Law1943 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1943.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation1977 :
    ¬ Law3272.TermDefinableFrom Law1977 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1977.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2128 :
    ¬ Law3272.TermDefinableFrom Law2128 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2128.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2135 :
    ¬ Law3272.TermDefinableFrom Law2135 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2135.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2167 :
    ¬ Law3272.TermDefinableFrom Law2167 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2167.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2170 :
    ¬ Law3272.TermDefinableFrom Law2170 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2170.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2180 :
    ¬ Law3272.TermDefinableFrom Law2180 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2180.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2196 :
    ¬ Law3272.TermDefinableFrom Law2196 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2196.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2291 :
    ¬ Law3272.TermDefinableFrom Law2291 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2291.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2335 :
    ¬ Law3272.TermDefinableFrom Law2335 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2335.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2349 :
    ¬ Law3272.TermDefinableFrom Law2349 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2349.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2373 :
    ¬ Law3272.TermDefinableFrom Law2373 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2373.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2399 :
    ¬ Law3272.TermDefinableFrom Law2399 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2399.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2494 :
    ¬ Law3272.TermDefinableFrom Law2494 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2494.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2519 :
    ¬ Law3272.TermDefinableFrom Law2519 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2519.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2522 :
    ¬ Law3272.TermDefinableFrom Law2522 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2522.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2573 :
    ¬ Law3272.TermDefinableFrom Law2573 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2573.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2576 :
    ¬ Law3272.TermDefinableFrom Law2576 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2576.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2917 :
    ¬ Law3272.TermDefinableFrom Law2917 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2917.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2925 :
    ¬ Law3272.TermDefinableFrom Law2925 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2925.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2944 :
    ¬ Law3272.TermDefinableFrom Law2944 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2944.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2947 :
    ¬ Law3272.TermDefinableFrom Law2947 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2947.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2958 :
    ¬ Law3272.TermDefinableFrom Law2958 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2958.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2979 :
    ¬ Law3272.TermDefinableFrom Law2979 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2979.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation2992 :
    ¬ Law3272.TermDefinableFrom Law2992 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2992.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3120 :
    ¬ Law3272.TermDefinableFrom Law3120 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3120.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3131 :
    ¬ Law3272.TermDefinableFrom Law3131 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3131.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3150 :
    ¬ Law3272.TermDefinableFrom Law3150 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3150.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3195 :
    ¬ Law3272.TermDefinableFrom Law3195 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3195.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3211 :
    ¬ Law3272.TermDefinableFrom Law3211 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3211.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3364 :
    ¬ Law3272.TermDefinableFrom Law3364 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3364.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3370 :
    ¬ Law3272.TermDefinableFrom Law3370 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3370.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3417 :
    ¬ Law3272.TermDefinableFrom Law3417 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3417.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3472 :
    ¬ Law3272.TermDefinableFrom Law3472 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3472.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3553 :
    ¬ Law3272.TermDefinableFrom Law3553 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3553.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3567 :
    ¬ Law3272.TermDefinableFrom Law3567 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3567.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3588 :
    ¬ Law3272.TermDefinableFrom Law3588 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3588.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3601 :
    ¬ Law3272.TermDefinableFrom Law3601 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3601.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3878 :
    ¬ Law3272.TermDefinableFrom Law3878 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3878.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation3994 :
    ¬ Law3272.TermDefinableFrom Law3994 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3994.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4007 :
    ¬ Law3272.TermDefinableFrom Law4007 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4007.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4013 :
    ¬ Law3272.TermDefinableFrom Law4013 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4013.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4026 :
    ¬ Law3272.TermDefinableFrom Law4026 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4026.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4162 :
    ¬ Law3272.TermDefinableFrom Law4162 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4162.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4182 :
    ¬ Law3272.TermDefinableFrom Law4182 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4182.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4216 :
    ¬ Law3272.TermDefinableFrom Law4216 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4216.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4273 :
    ¬ Law3272.TermDefinableFrom Law4273 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4273.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4305 :
    ¬ Law3272.TermDefinableFrom Law4305 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4305.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4332 :
    ¬ Law3272.TermDefinableFrom Law4332 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4332.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4386 :
    ¬ Law3272.TermDefinableFrom Law4386 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4386.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4413 :
    ¬ Law3272.TermDefinableFrom Law4413 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4413.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4421 :
    ¬ Law3272.TermDefinableFrom Law4421 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4421.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4446 :
    ¬ Law3272.TermDefinableFrom Law4446 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4446.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4450 :
    ¬ Law3272.TermDefinableFrom Law4450 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4450.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4458 :
    ¬ Law3272.TermDefinableFrom Law4458 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4458.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4588 :
    ¬ Law3272.TermDefinableFrom Law4588 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4588.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4640 :
    ¬ Law3272.TermDefinableFrom Law4640 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4640.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4647 :
    ¬ Law3272.TermDefinableFrom Law4647 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4647.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_3272 op hop ((@Law3272.models_iff ℤ (Magma.mk op)).mp h)

/-! ### Equation `4091` -/

theorem Equation4091_not_termDefinableFrom_Equation14 :
    ¬ Law4091.TermDefinableFrom Law14 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law14.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation29 :
    ¬ Law4091.TermDefinableFrom Law29 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law29.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation477 :
    ¬ Law4091.TermDefinableFrom Law477 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law477.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation489 :
    ¬ Law4091.TermDefinableFrom Law489 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law489.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation492 :
    ¬ Law4091.TermDefinableFrom Law492 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law492.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation522 :
    ¬ Law4091.TermDefinableFrom Law522 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law522.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation572 :
    ¬ Law4091.TermDefinableFrom Law572 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law572.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation680 :
    ¬ Law4091.TermDefinableFrom Law680 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law680.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation684 :
    ¬ Law4091.TermDefinableFrom Law684 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law684.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation692 :
    ¬ Law4091.TermDefinableFrom Law692 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law692.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation711 :
    ¬ Law4091.TermDefinableFrom Law711 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law711.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation725 :
    ¬ Law4091.TermDefinableFrom Law725 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law725.models_iff ℤ Magma.negInt).mpr negInt_satisfies_0.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation746 :
    ¬ Law4091.TermDefinableFrom Law746 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law746.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation759 :
    ¬ Law4091.TermDefinableFrom Law759 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law759.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1073 :
    ¬ Law4091.TermDefinableFrom Law1073 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1073.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1152 :
    ¬ Law4091.TermDefinableFrom Law1152 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1152.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1155 :
    ¬ Law4091.TermDefinableFrom Law1155 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1155.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1165 :
    ¬ Law4091.TermDefinableFrom Law1165 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1165.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1181 :
    ¬ Law4091.TermDefinableFrom Law1181 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1181.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1276 :
    ¬ Law4091.TermDefinableFrom Law1276 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1276.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1293 :
    ¬ Law4091.TermDefinableFrom Law1293 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1293.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1304 :
    ¬ Law4091.TermDefinableFrom Law1304 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1304.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1320 :
    ¬ Law4091.TermDefinableFrom Law1320 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1320.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1358 :
    ¬ Law4091.TermDefinableFrom Law1358 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1358.models_iff ℤ Magma.negInt).mpr negInt_satisfies_1.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1492 :
    ¬ Law4091.TermDefinableFrom Law1492 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1492.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1504 :
    ¬ Law4091.TermDefinableFrom Law1504 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1504.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1507 :
    ¬ Law4091.TermDefinableFrom Law1507 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1507.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1519 :
    ¬ Law4091.TermDefinableFrom Law1519 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1519.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1558 :
    ¬ Law4091.TermDefinableFrom Law1558 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1558.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1561 :
    ¬ Law4091.TermDefinableFrom Law1561 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1561.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1695 :
    ¬ Law4091.TermDefinableFrom Law1695 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1695.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1699 :
    ¬ Law4091.TermDefinableFrom Law1699 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1699.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1707 :
    ¬ Law4091.TermDefinableFrom Law1707 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1707.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1932 :
    ¬ Law4091.TermDefinableFrom Law1932 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1932.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1943 :
    ¬ Law4091.TermDefinableFrom Law1943 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1943.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation1977 :
    ¬ Law4091.TermDefinableFrom Law1977 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law1977.models_iff ℤ Magma.negInt).mpr negInt_satisfies_2.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2128 :
    ¬ Law4091.TermDefinableFrom Law2128 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2128.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2135 :
    ¬ Law4091.TermDefinableFrom Law2135 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2135.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2167 :
    ¬ Law4091.TermDefinableFrom Law2167 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2167.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2170 :
    ¬ Law4091.TermDefinableFrom Law2170 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2170.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2180 :
    ¬ Law4091.TermDefinableFrom Law2180 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2180.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2196 :
    ¬ Law4091.TermDefinableFrom Law2196 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2196.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2291 :
    ¬ Law4091.TermDefinableFrom Law2291 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2291.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2335 :
    ¬ Law4091.TermDefinableFrom Law2335 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2335.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2349 :
    ¬ Law4091.TermDefinableFrom Law2349 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2349.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2373 :
    ¬ Law4091.TermDefinableFrom Law2373 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2373.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2399 :
    ¬ Law4091.TermDefinableFrom Law2399 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2399.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2494 :
    ¬ Law4091.TermDefinableFrom Law2494 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2494.models_iff ℤ Magma.negInt).mpr negInt_satisfies_3.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2519 :
    ¬ Law4091.TermDefinableFrom Law2519 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2519.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2522 :
    ¬ Law4091.TermDefinableFrom Law2522 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2522.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2573 :
    ¬ Law4091.TermDefinableFrom Law2573 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2573.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2576 :
    ¬ Law4091.TermDefinableFrom Law2576 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2576.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2917 :
    ¬ Law4091.TermDefinableFrom Law2917 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2917.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2925 :
    ¬ Law4091.TermDefinableFrom Law2925 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2925.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2944 :
    ¬ Law4091.TermDefinableFrom Law2944 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2944.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2947 :
    ¬ Law4091.TermDefinableFrom Law2947 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2947.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2958 :
    ¬ Law4091.TermDefinableFrom Law2958 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2958.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2979 :
    ¬ Law4091.TermDefinableFrom Law2979 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2979.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation2992 :
    ¬ Law4091.TermDefinableFrom Law2992 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law2992.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3120 :
    ¬ Law4091.TermDefinableFrom Law3120 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3120.models_iff ℤ Magma.negInt).mpr negInt_satisfies_4.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3131 :
    ¬ Law4091.TermDefinableFrom Law3131 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3131.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3150 :
    ¬ Law4091.TermDefinableFrom Law3150 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3150.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3195 :
    ¬ Law4091.TermDefinableFrom Law3195 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3195.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3211 :
    ¬ Law4091.TermDefinableFrom Law3211 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3211.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3364 :
    ¬ Law4091.TermDefinableFrom Law3364 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3364.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3370 :
    ¬ Law4091.TermDefinableFrom Law3370 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3370.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3417 :
    ¬ Law4091.TermDefinableFrom Law3417 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3417.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3472 :
    ¬ Law4091.TermDefinableFrom Law3472 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3472.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3553 :
    ¬ Law4091.TermDefinableFrom Law3553 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3553.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3567 :
    ¬ Law4091.TermDefinableFrom Law3567 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3567.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3588 :
    ¬ Law4091.TermDefinableFrom Law3588 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3588.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3601 :
    ¬ Law4091.TermDefinableFrom Law3601 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3601.models_iff ℤ Magma.negInt).mpr negInt_satisfies_5.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3878 :
    ¬ Law4091.TermDefinableFrom Law3878 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3878.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation3994 :
    ¬ Law4091.TermDefinableFrom Law3994 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law3994.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4007 :
    ¬ Law4091.TermDefinableFrom Law4007 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4007.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4013 :
    ¬ Law4091.TermDefinableFrom Law4013 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4013.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4026 :
    ¬ Law4091.TermDefinableFrom Law4026 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4026.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4162 :
    ¬ Law4091.TermDefinableFrom Law4162 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4162.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4182 :
    ¬ Law4091.TermDefinableFrom Law4182 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4182.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4216 :
    ¬ Law4091.TermDefinableFrom Law4216 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4216.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4273 :
    ¬ Law4091.TermDefinableFrom Law4273 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4273.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4305 :
    ¬ Law4091.TermDefinableFrom Law4305 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4305.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4332 :
    ¬ Law4091.TermDefinableFrom Law4332 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4332.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4386 :
    ¬ Law4091.TermDefinableFrom Law4386 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4386.models_iff ℤ Magma.negInt).mpr negInt_satisfies_6.2.2.2.2.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4413 :
    ¬ Law4091.TermDefinableFrom Law4413 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4413.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4421 :
    ¬ Law4091.TermDefinableFrom Law4421 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4421.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4446 :
    ¬ Law4091.TermDefinableFrom Law4446 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4446.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4450 :
    ¬ Law4091.TermDefinableFrom Law4450 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4450.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4458 :
    ¬ Law4091.TermDefinableFrom Law4458 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4458.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4588 :
    ¬ Law4091.TermDefinableFrom Law4588 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4588.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4640 :
    ¬ Law4091.TermDefinableFrom Law4640 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4640.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.2.2.2.1)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4091_not_termDefinableFrom_Equation4647 :
    ¬ Law4091.TermDefinableFrom Law4647 :=
  not_termDefinableFrom_of_invariant Magma.negInt
    ((@Law4647.models_iff ℤ Magma.negInt).mpr negInt_satisfies_7.2.2.2.2.2.2.2)
    Magma.negInt_isCloneInvariant fun op hop h ↦
      Magma.negInt_refutes_4091 op hop ((@Law4091.models_iff ℤ (Magma.mk op)).mp h)
