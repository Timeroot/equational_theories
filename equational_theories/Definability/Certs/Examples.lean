import equational_theories.Definability.Certs.Affine3Sources
import equational_theories.Definability.Certs.Affine3Targets0
import equational_theories.Definability.Certs.Cyclic3Sources
import equational_theories.Definability.Certs.Cyclic3Targets0
import equational_theories.Definability.Certs.Fin2AllSources
import equational_theories.Definability.Certs.Fin2AllTargets0
import equational_theories.Definability.Certs.Fin2UnarySources
import equational_theories.Definability.Certs.Fin2UnaryTargets0
import equational_theories.Definability.Certs.Reflective3Sources
import equational_theories.Definability.Certs.Reflective3Targets0

/-!
# Reading a non-definability fact off the certificate tables

The certificate tables in this directory are conjunctions with one conjunct per equation, in the
same order as the lists that appear in their statements. A single non-definability fact is
obtained by projecting the relevant conjunct out of a source table and out of a target table and
feeding both to the matching `Law.MagmaLaw.not_definableFrom_*` lemma; `Lawn.models_iff` converts
between the `Equationn G` form used by the tables and the `G ⊧ Lawn` form used by the lemmas.

One example per certificate follows. Between them the five tables settle `7351315` of the
`4694 * 4694 = 22033636` ordered pairs, a third of the whole definability graph. The marginal
contributions are very uneven: `Magma.cyclic3` alone gives `5498608`, `Magma.reflective3` adds
`1367244`, `Magma.fin2Unary` adds `275975`, `Magma.fin2` adds `156160`, and `Magma.affine3` adds
only `53328`.
-/

open Law.MagmaLaw

/-- **Cardinality on `Fin 2`.** Equation 39, `x ◇ x = y ◇ x`, is satisfied by the constant
two-element magma; equation 15, `x = y ◇ (x ◇ z)`, has no two-element model at all. -/
theorem Equation15_not_definableFrom_Equation39 : ¬ Law15.DefinableFrom Law39 :=
  not_definableFrom_fin2 (a := 0) (b := 0) (c := 0) (d := 0)
    ((@Law39.models_iff (Fin 2) (Magma.fin2 0 0 0 0)).mpr fin2_satisfies_0_0_0_0.2.2.1)
    fun a b c d h ↦
      fin2_refutes_0.2.2.2.1 a b c d ((@Law15.models_iff (Fin 2) (Magma.fin2 a b c d)).mp h)

/-- **Two-element symmetry.** Equation 3, `x = x ◇ x`, is satisfied by `x ◇ y = x`, whose
automorphism group is all of `Sym (Fin 2)`; equation 14, `x = y ◇ (x ◇ y)`, is satisfied by none
of the four two-element magmas with that automorphism group, although it does have two-element
models. -/
theorem Equation14_not_definableFrom_Equation3 : ¬ Law14.DefinableFrom Law3 :=
  not_definableFrom_fin2Unary (i := 0)
    ((@Law3.models_iff (Fin 2) (Magma.fin2Unary 0)).mpr fin2Unary_satisfies_0.2.1)
    fun i h ↦
      fin2Unary_refutes_0.2.2.2.1 i ((@Law14.models_iff (Fin 2) (Magma.fin2Unary i)).mp h)

/-- **Cyclic symmetry on `Fin 3`.** Equation 4, `x = x ◇ y`, is satisfied by `x ◇ y = x`, which is
cyclically symmetric; equation 7, `x = y ◇ z`, is satisfied by none of the `27` cyclically
symmetric magmas on `Fin 3`. -/
theorem Equation7_not_definableFrom_Equation4 : ¬ Law7.DefinableFrom Law4 :=
  not_definableFrom_cyclic3 (a := 0) (b := 0) (c := 0)
    ((@Law4.models_iff (Fin 3) (Magma.cyclic3 0 0 0)).mpr cyclic3_satisfies_0_0_0.2.2.1)
    fun a b c h ↦
      cyclic3_refutes_0.2.2.1 a b c ((@Law7.models_iff (Fin 3) (Magma.cyclic3 a b c)).mp h)

/-- **Reflection symmetry on `Fin 3`.** Equation 38, `x ◇ x = x ◇ y`, is satisfied by the constant
magma on `Fin 3`, which is reflective; equation 17, `x = y ◇ (y ◇ y)`, is satisfied by none of the
`81` reflective magmas on `Fin 3`. -/
theorem Equation17_not_definableFrom_Equation38 : ¬ Law17.DefinableFrom Law38 :=
  not_definableFrom_reflective3 (a := 0) (b := 0) (c := 0) (d := 0)
    ((@Law38.models_iff (Fin 3) (Magma.reflective3 0 0 0 0)).mpr reflective3_satisfies_0_0_0_0.2.1)
    fun a b c d h ↦
      reflective3_refutes_0.2.2.2.2.1 a b c d
        ((@Law17.models_iff (Fin 3) (Magma.reflective3 a b c d)).mp h)

/-- **Full symmetry on `Fin 3`.** Equation 8, `x = x ◇ (x ◇ x)`, is satisfied by `x ◇ y = x`, whose
automorphism group is all of `S₃`; equation 18, `x = y ◇ (y ◇ z)`, is satisfied by none of the `3`
affine magmas on `Fin 3`. -/
theorem Equation18_not_definableFrom_Equation8 : ¬ Law18.DefinableFrom Law8 :=
  not_definableFrom_affine3 (c := 0)
    ((@Law8.models_iff (Fin 3) (Magma.affine3 0)).mpr affine3_satisfies_0.2.2.2.1)
    fun c h ↦
      affine3_refutes_0.2.2.2.2.2.1 c ((@Law18.models_iff (Fin 3) (Magma.affine3 c)).mp h)
