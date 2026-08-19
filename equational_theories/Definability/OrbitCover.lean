import equational_theories.Definability.Orbit
import equational_theories.Equations.All

/-!
# The orbit certificates

Refutations discharged by the orbit clone family of `Definability/Orbit.lean` on the carrier
`Fin 4`. Unlike `Definability/Regular.lean` there is no group action here at all: the clone
conditions only ask that each `act x y` be an *endomorphism* of the model, so the index may be a
generating set of the sixteen pairs under `End M` rather than a transversal of the orbits of
`Aut M`. That is six representatives instead of eight, and the family is `Fin 6 → Fin 4`, of size
`4096` rather than `65536`.

The `act` matrix uses only three kinds of map: the identity, the reversal `x ↦ 3 - x`, and the four
constants. The reversal is an automorphism of both tables below, and the constants are
endomorphisms because both tables have an idempotent diagonal.

| certificate | carrier | table | family | sources | targets |
| --- | --- | --- | --- | --- | --- |
| `Magma.orbCertA` | `Fin 4` | `0011 2133 0021 2233` | `4096` | `1682`, `3675` | `43`, `332`, `3342`, `3545`, `4343` |
| `Magma.orbCertB` | `Fin 4` | `0011 2103 0321 2233` | `4096` | `4405` | `3342`, `3545` |

The refutation theorems depend only on the carrier, the representative data and the target, so all
three sources share them: `Magma.orbCertB` costs one table, one `decide` and one `native_decide`
and no refutation of its own. That is the whole economy of describing a clone by a formula — the
expensive half is stated once and reused.

The family is deliberately larger than the operations invariant under the symmetries: an assignment
whose value at a representative is not consistent with the maps out of it decodes to an operation
that is not itself equivariant, and `decode` still produces an operation. A clone family only has
to be a superset of the clone, and it is the larger set that is refuted below.

`Magma.orbCertB` re-refutes the two cells that `Magma.regCert3` of `Definability/RegularCover.lean`
already closes over `ZMod 6`; it is kept because it is nearly free and shows that one `Fin 4`
family reaches three sources.

These are not instances of the commuting-term argument of `Definability/FPF.lean`, which needs the
target to prove `W x y = W y x`; none of these five targets does.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace Magma

/-! ### The representative data on `Fin 4` -/

/-- Which of the six representatives the pair `(x, y)` is generated from. -/
def endo4Rep : Fin 4 → Fin 4 → Fin 6 :=
  ![![0, 0, 1, 2],
    ![3, 0, 4, 5],
    ![5, 4, 0, 3],
    ![2, 1, 0, 0]]

/-- The endomorphism carrying the value at the representative of `endo4Rep x y` to the value at
`(x, y)`: the identity, the reversal `x ↦ 3 - x`, or a constant. -/
def endo4Act : Fin 4 → Fin 4 → Fin 4 → Fin 4 :=
  ![![![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]],
    ![![0, 1, 2, 3], ![1, 1, 1, 1], ![0, 1, 2, 3], ![0, 1, 2, 3]],
    ![![3, 2, 1, 0], ![3, 2, 1, 0], ![2, 2, 2, 2], ![3, 2, 1, 0]],
    ![![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 3, 3, 3]]]

/-- The six representatives `(0,1)`, `(0,2)`, `(0,3)`, `(1,0)`, `(1,2)`, `(1,3)` of the pairs of
`Fin 4` under the endomorphisms above. -/
def endo4RepData : RepData (Fin 4) (Fin 6) where
  rep := endo4Rep
  act := endo4Act

/-- The assignment that decodes to the first projection: the first coordinates of the six
representatives. -/
def endo4Fst : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 1]

/-- The assignment that decodes to the second projection: the second coordinates of the six
representatives. -/
def endo4Snd : Fin 6 → Fin 4 := ![1, 2, 3, 0, 2, 3]

theorem endo4Rep_fst :
    ∀ x y : Fin 4, endo4RepData.act x y (endo4Fst (endo4RepData.rep x y)) = x := by decide

theorem endo4Rep_snd :
    ∀ x y : Fin 4, endo4RepData.act x y (endo4Snd (endo4RepData.rep x y)) = y := by decide

/-! ### The two models -/

/-- Values at the six representatives of the magma on `Fin 4` with table

    [[0, 0, 1, 1],
     [2, 1, 3, 3],
     [0, 0, 2, 1],
     [2, 2, 3, 3]]

which models both `1682` and `3675`. -/
def orbCertA : Fin 6 → Fin 4 := ![0, 1, 1, 2, 3, 3]

/-- Values at the six representatives of the magma on `Fin 4` with table

    [[0, 0, 1, 1],
     [2, 1, 0, 3],
     [0, 3, 2, 1],
     [2, 2, 3, 3]]

which models `4405`. -/
def orbCertB : Fin 6 → Fin 4 := ![0, 1, 1, 2, 0, 3]

theorem orbCertA_isEndo :
    ∀ x y : Fin 4, (endo4RepData.decode orbCertA).IsEndo (endo4RepData.act x y) := by decide

theorem orbCertB_isEndo :
    ∀ x y : Fin 4, (endo4RepData.decode orbCertB).IsEndo (endo4RepData.act x y) := by decide

end Magma

/-! ### The targets no operation decoded from the `Fin 4` representative data satisfies -/

theorem orbEndo4_refutes_43 :
    ∀ i : Fin 6 → Fin 4, ¬ @Equation43 (Fin 4) (Magma.endo4RepData.decode i) := by
  native_decide

theorem orbEndo4_refutes_332 :
    ∀ i : Fin 6 → Fin 4, ¬ @Equation332 (Fin 4) (Magma.endo4RepData.decode i) := by
  native_decide

theorem orbEndo4_refutes_3342 :
    ∀ i : Fin 6 → Fin 4, ¬ @Equation3342 (Fin 4) (Magma.endo4RepData.decode i) := by
  native_decide

theorem orbEndo4_refutes_3545 :
    ∀ i : Fin 6 → Fin 4, ¬ @Equation3545 (Fin 4) (Magma.endo4RepData.decode i) := by
  native_decide

theorem orbEndo4_refutes_4343 :
    ∀ i : Fin 6 → Fin 4, ¬ @Equation4343 (Fin 4) (Magma.endo4RepData.decode i) := by
  native_decide

/-! ### `Magma.orbCertA`, sources `1682` and `3675` -/

theorem orbCertA_satisfies_1682 :
    @Equation1682 (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA) := by decide

theorem orbCertA_satisfies_3675 :
    @Equation3675 (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA) := by decide

theorem Equation43_not_termDefinableFromFin_Equation1682 :
    ¬ Law43.TermDefinableFromFin Law1682 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law1682.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_1682)
    fun i hi ↦ orbEndo4_refutes_43 i
      ((@Law43.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation332_not_termDefinableFromFin_Equation1682 :
    ¬ Law332.TermDefinableFromFin Law1682 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law1682.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_1682)
    fun i hi ↦ orbEndo4_refutes_332 i
      ((@Law332.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation3342_not_termDefinableFromFin_Equation1682 :
    ¬ Law3342.TermDefinableFromFin Law1682 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law1682.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_1682)
    fun i hi ↦ orbEndo4_refutes_3342 i
      ((@Law3342.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation3545_not_termDefinableFromFin_Equation1682 :
    ¬ Law3545.TermDefinableFromFin Law1682 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law1682.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_1682)
    fun i hi ↦ orbEndo4_refutes_3545 i
      ((@Law3545.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation4343_not_termDefinableFromFin_Equation1682 :
    ¬ Law4343.TermDefinableFromFin Law1682 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law1682.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_1682)
    fun i hi ↦ orbEndo4_refutes_4343 i
      ((@Law4343.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation43_not_termDefinableFromFin_Equation3675 :
    ¬ Law43.TermDefinableFromFin Law3675 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law3675.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_3675)
    fun i hi ↦ orbEndo4_refutes_43 i
      ((@Law43.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation332_not_termDefinableFromFin_Equation3675 :
    ¬ Law332.TermDefinableFromFin Law3675 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law3675.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_3675)
    fun i hi ↦ orbEndo4_refutes_332 i
      ((@Law332.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation3342_not_termDefinableFromFin_Equation3675 :
    ¬ Law3342.TermDefinableFromFin Law3675 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law3675.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_3675)
    fun i hi ↦ orbEndo4_refutes_3342 i
      ((@Law3342.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation3545_not_termDefinableFromFin_Equation3675 :
    ¬ Law3545.TermDefinableFromFin Law3675 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law3675.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_3675)
    fun i hi ↦ orbEndo4_refutes_3545 i
      ((@Law3545.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation4343_not_termDefinableFromFin_Equation3675 :
    ¬ Law4343.TermDefinableFromFin Law3675 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertA Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertA_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law3675.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertA)).mpr
      orbCertA_satisfies_3675)
    fun i hi ↦ orbEndo4_refutes_4343 i
      ((@Law4343.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

/-! ### `Magma.orbCertB`, source `4405`

Both cells are already closed by `Magma.regCert3` over `ZMod 6`; these are a second, independent
witness on a carrier a third of the size. -/

theorem orbCertB_satisfies_4405 :
    @Equation4405 (Fin 4) (Magma.endo4RepData.decode Magma.orbCertB) := by decide

theorem Equation3342_not_termDefinableFromFin_Equation4405_endo4 :
    ¬ Law3342.TermDefinableFromFin Law4405 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertB Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertB_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law4405.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertB)).mpr
      orbCertB_satisfies_4405)
    fun i hi ↦ orbEndo4_refutes_3342 i
      ((@Law3342.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)

theorem Equation3545_not_termDefinableFromFin_Equation4405_endo4 :
    ¬ Law3545.TermDefinableFromFin Law4405 :=
  not_termDefinableFromFin_of_repData Magma.endo4RepData Magma.orbCertB Magma.endo4Fst
    Magma.endo4Snd Magma.orbCertB_isEndo Magma.endo4Rep_fst Magma.endo4Rep_snd
    ((@Law4405.models_iff (Fin 4) (Magma.endo4RepData.decode Magma.orbCertB)).mpr
      orbCertB_satisfies_4405)
    fun i hi ↦ orbEndo4_refutes_3545 i
      ((@Law3545.models_iff (Fin 4) (Magma.endo4RepData.decode i)).mp hi)
