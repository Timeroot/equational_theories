import equational_theories.Definability.Regular
import equational_theories.Equations.All

/-!
# The regular certificates

Refutations discharged by the regular clone family of `Definability/Regular.lean`: a magma
`x ◇ y = x + h₀ (-x + y)` on a finite group, whose clone is contained in the family of *all* such
operations, so that a target is refuted by a single quantifier over the type of `h₀`.

| certificate | carrier | `h₀` | family | source | targets |
| --- | --- | --- | --- | --- | --- |
| `Magma.regCert1` | `ZMod 5` | `11310` | `3125` | `4415` | `313`, `3272`, `3472`, `3588`, `4273` |
| `Magma.regCert2` | `ZMod 6` | `002205` | `46656` | `4443` | `43`, `332`, `3342`, `3545`, `4321`, `4343` |
| `Magma.regCert3` | `ZMod 6` | `002105` | `46656` | `4405` | `3342`, `3545` |

Forty-six thousand operations is two orders of magnitude past the largest *listed* clone in this
development (`Magma.negCert40Clone`, at 324, and `Definability/CloneExtra6.lean` spends three
thousand lines on it). None of them is written down. What is checked is
`∀ h : ZMod n → ZMod n, ¬ Equation_ (ZMod n) (Magma.transOp h)`, and that is `native_decide`.

The refutation theorems below depend only on the carrier and the target, not on `h₀`, so the two
`ZMod 6` certificates share theirs: the family is the same family. That is the point of describing
a clone by a formula — the expensive half of the certificate is reusable, and only the cheap half,
the source, has to be reproved.

`4415`, `4443` and `4405` are among the heaviest sources on the definability board. The witnesses
are finite, so each refutation is stated against `Law.MagmaLaw.TermDefinableFromFin`, from which the
all-magmas refutation follows by contraposing `Law.MagmaLaw.termDefinableFin_of_termDefinable`.

## Adding another certificate

One `def` for `h₀`, one theorem for the source, one `refutes` theorem per (carrier, target) pair not
already covered, and one conclusion apiece. Nothing in `Definability/Regular.lean` changes, no
composition table is ever computed, and the carrier may be any finite additive group.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

namespace Magma

/-- `h₀` for the regular magma on `ZMod 5` with table

    [[1, 1, 3, 1, 0],
     [1, 2, 2, 4, 2],
     [3, 2, 3, 3, 0],
     [1, 4, 3, 4, 4],
     [0, 2, 0, 4, 0]]

which models `4415`. -/
@[implicit_reducible]
def regCert1 : ZMod 5 → ZMod 5 := ![1, 1, 3, 1, 0]

/-- `h₀` for the regular magma on `ZMod 6` with table

    [[0, 0, 2, 2, 0, 5],
     [0, 1, 1, 3, 3, 1],
     [2, 1, 2, 2, 4, 4],
     [5, 3, 2, 3, 3, 5],
     [0, 0, 4, 3, 4, 4],
     [5, 1, 1, 5, 4, 5]]

which models `4443`. -/
@[implicit_reducible]
def regCert2 : ZMod 6 → ZMod 6 := ![0, 0, 2, 2, 0, 5]

/-- `h₀` for the regular magma on `ZMod 6` with table

    [[0, 0, 2, 1, 0, 5],
     [0, 1, 1, 3, 2, 1],
     [2, 1, 2, 2, 4, 3],
     [4, 3, 2, 3, 3, 5],
     [0, 5, 4, 3, 4, 4],
     [5, 1, 0, 5, 4, 5]]

which models `4405`. -/
@[implicit_reducible]
def regCert3 : ZMod 6 → ZMod 6 := ![0, 0, 2, 1, 0, 5]

end Magma

/-! ### The targets no regular operation on `ZMod 5` satisfies -/

theorem regZ5_refutes_313 :
    ∀ h : ZMod 5 → ZMod 5, ¬ @Equation313 (ZMod 5) (Magma.transOp h) := by native_decide

theorem regZ5_refutes_3272 :
    ∀ h : ZMod 5 → ZMod 5, ¬ @Equation3272 (ZMod 5) (Magma.transOp h) := by native_decide

theorem regZ5_refutes_3472 :
    ∀ h : ZMod 5 → ZMod 5, ¬ @Equation3472 (ZMod 5) (Magma.transOp h) := by native_decide

theorem regZ5_refutes_3588 :
    ∀ h : ZMod 5 → ZMod 5, ¬ @Equation3588 (ZMod 5) (Magma.transOp h) := by native_decide

theorem regZ5_refutes_4273 :
    ∀ h : ZMod 5 → ZMod 5, ¬ @Equation4273 (ZMod 5) (Magma.transOp h) := by native_decide

/-! ### The targets no regular operation on `ZMod 6` satisfies -/

theorem regZ6_refutes_43 :
    ∀ h : ZMod 6 → ZMod 6, ¬ @Equation43 (ZMod 6) (Magma.transOp h) := by native_decide

theorem regZ6_refutes_332 :
    ∀ h : ZMod 6 → ZMod 6, ¬ @Equation332 (ZMod 6) (Magma.transOp h) := by native_decide

theorem regZ6_refutes_3342 :
    ∀ h : ZMod 6 → ZMod 6, ¬ @Equation3342 (ZMod 6) (Magma.transOp h) := by native_decide

theorem regZ6_refutes_3545 :
    ∀ h : ZMod 6 → ZMod 6, ¬ @Equation3545 (ZMod 6) (Magma.transOp h) := by native_decide

theorem regZ6_refutes_4321 :
    ∀ h : ZMod 6 → ZMod 6, ¬ @Equation4321 (ZMod 6) (Magma.transOp h) := by native_decide

theorem regZ6_refutes_4343 :
    ∀ h : ZMod 6 → ZMod 6, ¬ @Equation4343 (ZMod 6) (Magma.transOp h) := by native_decide

/-! ### `Magma.regCert1`, source `4415` -/

theorem regCert1_satisfies_4415 :
    @Equation4415 (ZMod 5) (Magma.transOp Magma.regCert1) := by native_decide

theorem Equation313_not_termDefinableFromFin_Equation4415 :
    ¬ Law313.TermDefinableFromFin Law4415 :=
  not_termDefinableFromFin_of_transClone Magma.regCert1
    ((@Law4415.models_iff (ZMod 5) (Magma.transOp Magma.regCert1)).mpr regCert1_satisfies_4415)
    fun h hh ↦ regZ5_refutes_313 h
      ((@Law313.models_iff (ZMod 5) (Magma.transOp h)).mp hh)

theorem Equation3272_not_termDefinableFromFin_Equation4415 :
    ¬ Law3272.TermDefinableFromFin Law4415 :=
  not_termDefinableFromFin_of_transClone Magma.regCert1
    ((@Law4415.models_iff (ZMod 5) (Magma.transOp Magma.regCert1)).mpr regCert1_satisfies_4415)
    fun h hh ↦ regZ5_refutes_3272 h
      ((@Law3272.models_iff (ZMod 5) (Magma.transOp h)).mp hh)

theorem Equation3472_not_termDefinableFromFin_Equation4415 :
    ¬ Law3472.TermDefinableFromFin Law4415 :=
  not_termDefinableFromFin_of_transClone Magma.regCert1
    ((@Law4415.models_iff (ZMod 5) (Magma.transOp Magma.regCert1)).mpr regCert1_satisfies_4415)
    fun h hh ↦ regZ5_refutes_3472 h
      ((@Law3472.models_iff (ZMod 5) (Magma.transOp h)).mp hh)

theorem Equation3588_not_termDefinableFromFin_Equation4415 :
    ¬ Law3588.TermDefinableFromFin Law4415 :=
  not_termDefinableFromFin_of_transClone Magma.regCert1
    ((@Law4415.models_iff (ZMod 5) (Magma.transOp Magma.regCert1)).mpr regCert1_satisfies_4415)
    fun h hh ↦ regZ5_refutes_3588 h
      ((@Law3588.models_iff (ZMod 5) (Magma.transOp h)).mp hh)

theorem Equation4273_not_termDefinableFromFin_Equation4415 :
    ¬ Law4273.TermDefinableFromFin Law4415 :=
  not_termDefinableFromFin_of_transClone Magma.regCert1
    ((@Law4415.models_iff (ZMod 5) (Magma.transOp Magma.regCert1)).mpr regCert1_satisfies_4415)
    fun h hh ↦ regZ5_refutes_4273 h
      ((@Law4273.models_iff (ZMod 5) (Magma.transOp h)).mp hh)

/-! ### `Magma.regCert2`, source `4443` -/

theorem regCert2_satisfies_4443 :
    @Equation4443 (ZMod 6) (Magma.transOp Magma.regCert2) := by native_decide

theorem Equation43_not_termDefinableFromFin_Equation4443 :
    ¬ Law43.TermDefinableFromFin Law4443 :=
  not_termDefinableFromFin_of_transClone Magma.regCert2
    ((@Law4443.models_iff (ZMod 6) (Magma.transOp Magma.regCert2)).mpr regCert2_satisfies_4443)
    fun h hh ↦ regZ6_refutes_43 h
      ((@Law43.models_iff (ZMod 6) (Magma.transOp h)).mp hh)

theorem Equation332_not_termDefinableFromFin_Equation4443 :
    ¬ Law332.TermDefinableFromFin Law4443 :=
  not_termDefinableFromFin_of_transClone Magma.regCert2
    ((@Law4443.models_iff (ZMod 6) (Magma.transOp Magma.regCert2)).mpr regCert2_satisfies_4443)
    fun h hh ↦ regZ6_refutes_332 h
      ((@Law332.models_iff (ZMod 6) (Magma.transOp h)).mp hh)

theorem Equation3342_not_termDefinableFromFin_Equation4443 :
    ¬ Law3342.TermDefinableFromFin Law4443 :=
  not_termDefinableFromFin_of_transClone Magma.regCert2
    ((@Law4443.models_iff (ZMod 6) (Magma.transOp Magma.regCert2)).mpr regCert2_satisfies_4443)
    fun h hh ↦ regZ6_refutes_3342 h
      ((@Law3342.models_iff (ZMod 6) (Magma.transOp h)).mp hh)

theorem Equation3545_not_termDefinableFromFin_Equation4443 :
    ¬ Law3545.TermDefinableFromFin Law4443 :=
  not_termDefinableFromFin_of_transClone Magma.regCert2
    ((@Law4443.models_iff (ZMod 6) (Magma.transOp Magma.regCert2)).mpr regCert2_satisfies_4443)
    fun h hh ↦ regZ6_refutes_3545 h
      ((@Law3545.models_iff (ZMod 6) (Magma.transOp h)).mp hh)

theorem Equation4321_not_termDefinableFromFin_Equation4443 :
    ¬ Law4321.TermDefinableFromFin Law4443 :=
  not_termDefinableFromFin_of_transClone Magma.regCert2
    ((@Law4443.models_iff (ZMod 6) (Magma.transOp Magma.regCert2)).mpr regCert2_satisfies_4443)
    fun h hh ↦ regZ6_refutes_4321 h
      ((@Law4321.models_iff (ZMod 6) (Magma.transOp h)).mp hh)

theorem Equation4343_not_termDefinableFromFin_Equation4443 :
    ¬ Law4343.TermDefinableFromFin Law4443 :=
  not_termDefinableFromFin_of_transClone Magma.regCert2
    ((@Law4443.models_iff (ZMod 6) (Magma.transOp Magma.regCert2)).mpr regCert2_satisfies_4443)
    fun h hh ↦ regZ6_refutes_4343 h
      ((@Law4343.models_iff (ZMod 6) (Magma.transOp h)).mp hh)

/-! ### `Magma.regCert3`, source `4405` -/

theorem regCert3_satisfies_4405 :
    @Equation4405 (ZMod 6) (Magma.transOp Magma.regCert3) := by native_decide

theorem Equation3342_not_termDefinableFromFin_Equation4405 :
    ¬ Law3342.TermDefinableFromFin Law4405 :=
  not_termDefinableFromFin_of_transClone Magma.regCert3
    ((@Law4405.models_iff (ZMod 6) (Magma.transOp Magma.regCert3)).mpr regCert3_satisfies_4405)
    fun h hh ↦ regZ6_refutes_3342 h
      ((@Law3342.models_iff (ZMod 6) (Magma.transOp h)).mp hh)

theorem Equation3545_not_termDefinableFromFin_Equation4405 :
    ¬ Law3545.TermDefinableFromFin Law4405 :=
  not_termDefinableFromFin_of_transClone Magma.regCert3
    ((@Law4405.models_iff (ZMod 6) (Magma.transOp Magma.regCert3)).mpr regCert3_satisfies_4405)
    fun h hh ↦ regZ6_refutes_3545 h
      ((@Law3545.models_iff (ZMod 6) (Magma.transOp h)).mp hh)
