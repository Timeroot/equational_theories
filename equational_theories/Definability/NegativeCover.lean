import equational_theories.Definability.CloneCerts
import equational_theories.Definability.Certificates

/-!
# A cover of the term-definability refutations

396 base non-definability facts, each discharged by one of the clone certificates of
`Definability/CloneCerts.lean`. Under the transitive closure of the definability order —
`¬ (L ≤ L')` gives `¬ (T ≤ S)` for every `T` from which `L` is definable and every `S`
definable from `L'` — the pairs below close `7394506` cells, and together with the
symmetry certificates tabulated in `Definability/Certs/` they close `7638678` of the
`4694 * 4694`.

Only the pairs that the symmetry families do *not* already reach are listed here: those
families refute first-order definability outright, which is strictly stronger, so a pair
inside one of their rectangles needs no clone certificate. That is why this cover is much
smaller than the number of refutations it is responsible for.

The larger checks are `native_decide`, which is worth stating plainly: the affine
certificates on `Fin 13`, `Fin 16`, `Fin 17` and `Fin 19` ask for hundreds of thousands of
law evaluations apiece, and the kernel needs gigabytes to do what compiled code does in a
second. So the refutations resting on those certificates additionally depend on
`Lean.ofReduceBool`.

This file is generated.
-/

set_option maxHeartbeats 4000000

open Law Law.MagmaLaw

/-! ### `Magma.negCert1` -/

theorem negCert1_satisfies_508 : @Equation508 (Fin 3) Magma.negCert1 := by decide!

theorem negCert1_refutes_464 : ∀ i, ¬ @Equation464 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_477 : ∀ i, ¬ @Equation477 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_511 : ∀ i, ¬ @Equation511 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_680 : ∀ i, ¬ @Equation680 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_707 : ∀ i, ¬ @Equation707 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_870 : ∀ i, ¬ @Equation870 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_917 : ∀ i, ¬ @Equation917 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_1086 : ∀ i, ¬ @Equation1086 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_1113 : ∀ i, ¬ @Equation1113 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_1276 : ∀ i, ¬ @Equation1276 (Fin 3) (Magma.negCert1Clone i) := by
  decide!
theorem negCert1_refutes_1289 : ∀ i, ¬ @Equation1289 (Fin 3) (Magma.negCert1Clone i) := by
  decide!

theorem Equation1113_not_termDefinableFrom_Equation508 :
    ¬ Law1113.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_1113 i
      ((@Law1113.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation707_not_termDefinableFrom_Equation508 :
    ¬ Law707.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_707 i
      ((@Law707.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation477_not_termDefinableFrom_Equation508 :
    ¬ Law477.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_477 i
      ((@Law477.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation680_not_termDefinableFrom_Equation508 :
    ¬ Law680.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_680 i
      ((@Law680.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation1086_not_termDefinableFrom_Equation508 :
    ¬ Law1086.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_1086 i
      ((@Law1086.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation1276_not_termDefinableFrom_Equation508 :
    ¬ Law1276.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_1276 i
      ((@Law1276.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation870_not_termDefinableFrom_Equation508 :
    ¬ Law870.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_870 i
      ((@Law870.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation917_not_termDefinableFrom_Equation508 :
    ¬ Law917.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_917 i
      ((@Law917.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation511_not_termDefinableFrom_Equation508 :
    ¬ Law511.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_511 i
      ((@Law511.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation464_not_termDefinableFrom_Equation508 :
    ¬ Law464.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_464 i
      ((@Law464.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

theorem Equation1289_not_termDefinableFrom_Equation508 :
    ¬ Law1289.TermDefinableFrom Law508 :=
  not_termDefinableFrom_of_clone Magma.negCert1
    ((@Law508.models_iff (Fin 3) Magma.negCert1).mpr negCert1_satisfies_508)
    Magma.negCert1_isCloneFamily fun i h ↦ negCert1_refutes_1289 i
      ((@Law1289.models_iff (Fin 3) (Magma.negCert1Clone i)).mp h)

/-! ### `Magma.negCert2` -/

theorem negCert2_satisfies_168 : @Equation168 (Fin 4) Magma.negCert2 := by decide!

theorem negCert2_refutes_66 : ∀ i, ¬ @Equation66 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_73 : ∀ i, ¬ @Equation73 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_118 : ∀ i, ¬ @Equation118 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_335 : ∀ i, ¬ @Equation335 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_464 : ∀ i, ¬ @Equation464 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_467 : ∀ i, ¬ @Equation467 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_474 : ∀ i, ¬ @Equation474 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_477 : ∀ i, ¬ @Equation477 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_501 : ∀ i, ¬ @Equation501 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_504 : ∀ i, ¬ @Equation504 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_511 : ∀ i, ¬ @Equation511 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_667 : ∀ i, ¬ @Equation667 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_670 : ∀ i, ¬ @Equation670 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_677 : ∀ i, ¬ @Equation677 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_680 : ∀ i, ¬ @Equation680 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_704 : ∀ i, ¬ @Equation704 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_707 : ∀ i, ¬ @Equation707 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_870 : ∀ i, ¬ @Equation870 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_873 : ∀ i, ¬ @Equation873 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_883 : ∀ i, ¬ @Equation883 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_907 : ∀ i, ¬ @Equation907 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_917 : ∀ i, ¬ @Equation917 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1076 : ∀ i, ¬ @Equation1076 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1086 : ∀ i, ¬ @Equation1086 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1110 : ∀ i, ¬ @Equation1110 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1113 : ∀ i, ¬ @Equation1113 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1276 : ∀ i, ¬ @Equation1276 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1279 : ∀ i, ¬ @Equation1279 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1286 : ∀ i, ¬ @Equation1286 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1289 : ∀ i, ¬ @Equation1289 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1313 : ∀ i, ¬ @Equation1313 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1489 : ∀ i, ¬ @Equation1489 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1516 : ∀ i, ¬ @Equation1516 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1519 : ∀ i, ¬ @Equation1519 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1526 : ∀ i, ¬ @Equation1526 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1682 : ∀ i, ¬ @Equation1682 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1685 : ∀ i, ¬ @Equation1685 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1692 : ∀ i, ¬ @Equation1692 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_1722 : ∀ i, ¬ @Equation1722 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3269 : ∀ i, ¬ @Equation3269 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3272 : ∀ i, ¬ @Equation3272 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3279 : ∀ i, ¬ @Equation3279 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3342 : ∀ i, ¬ @Equation3342 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3345 : ∀ i, ¬ @Equation3345 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3352 : ∀ i, ¬ @Equation3352 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3355 : ∀ i, ¬ @Equation3355 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3472 : ∀ i, ¬ @Equation3472 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3475 : ∀ i, ¬ @Equation3475 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3482 : ∀ i, ¬ @Equation3482 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3545 : ∀ i, ¬ @Equation3545 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3548 : ∀ i, ¬ @Equation3548 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3555 : ∀ i, ¬ @Equation3555 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3558 : ∀ i, ¬ @Equation3558 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3675 : ∀ i, ¬ @Equation3675 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3678 : ∀ i, ¬ @Equation3678 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_3748 : ∀ i, ¬ @Equation3748 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_4273 : ∀ i, ¬ @Equation4273 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_4290 : ∀ i, ¬ @Equation4290 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_4405 : ∀ i, ¬ @Equation4405 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_4408 : ∀ i, ¬ @Equation4408 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_4443 : ∀ i, ¬ @Equation4443 (Fin 4) (Magma.negCert2Clone i) := by
  decide!
theorem negCert2_refutes_4482 : ∀ i, ¬ @Equation4482 (Fin 4) (Magma.negCert2Clone i) := by
  decide!

theorem Equation4273_not_termDefinableFrom_Equation168 :
    ¬ Law4273.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_4273 i
      ((@Law4273.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation4405_not_termDefinableFrom_Equation168 :
    ¬ Law4405.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_4405 i
      ((@Law4405.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation4290_not_termDefinableFrom_Equation168 :
    ¬ Law4290.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_4290 i
      ((@Law4290.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1526_not_termDefinableFrom_Equation168 :
    ¬ Law1526.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1526 i
      ((@Law1526.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation511_not_termDefinableFrom_Equation168 :
    ¬ Law511.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_511 i
      ((@Law511.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3472_not_termDefinableFrom_Equation168 :
    ¬ Law3472.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3472 i
      ((@Law3472.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation504_not_termDefinableFrom_Equation168 :
    ¬ Law504.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_504 i
      ((@Law504.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation707_not_termDefinableFrom_Equation168 :
    ¬ Law707.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_707 i
      ((@Law707.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1086_not_termDefinableFrom_Equation168 :
    ¬ Law1086.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1086 i
      ((@Law1086.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1113_not_termDefinableFrom_Equation168 :
    ¬ Law1113.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1113 i
      ((@Law1113.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1519_not_termDefinableFrom_Equation168 :
    ¬ Law1519.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1519 i
      ((@Law1519.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation680_not_termDefinableFrom_Equation168 :
    ¬ Law680.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_680 i
      ((@Law680.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation73_not_termDefinableFrom_Equation168 :
    ¬ Law73.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_73 i
      ((@Law73.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1685_not_termDefinableFrom_Equation168 :
    ¬ Law1685.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1685 i
      ((@Law1685.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation66_not_termDefinableFrom_Equation168 :
    ¬ Law66.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_66 i
      ((@Law66.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation873_not_termDefinableFrom_Equation168 :
    ¬ Law873.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_873 i
      ((@Law873.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation4408_not_termDefinableFrom_Equation168 :
    ¬ Law4408.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_4408 i
      ((@Law4408.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation168 :
    ¬ Law3342.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3342 i
      ((@Law3342.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation168 :
    ¬ Law3545.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3545 i
      ((@Law3545.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation4482_not_termDefinableFrom_Equation168 :
    ¬ Law4482.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_4482 i
      ((@Law4482.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation335_not_termDefinableFrom_Equation168 :
    ¬ Law335.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_335 i
      ((@Law335.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation168 :
    ¬ Law3269.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3269 i
      ((@Law3269.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation168 :
    ¬ Law3279.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3279 i
      ((@Law3279.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation168 :
    ¬ Law3345.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3345 i
      ((@Law3345.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3352_not_termDefinableFrom_Equation168 :
    ¬ Law3352.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3352 i
      ((@Law3352.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation168 :
    ¬ Law3475.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3475 i
      ((@Law3475.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation168 :
    ¬ Law3482.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3482 i
      ((@Law3482.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation168 :
    ¬ Law3548.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3548 i
      ((@Law3548.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3558_not_termDefinableFrom_Equation168 :
    ¬ Law3558.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3558 i
      ((@Law3558.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3748_not_termDefinableFrom_Equation168 :
    ¬ Law3748.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3748 i
      ((@Law3748.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation464_not_termDefinableFrom_Equation168 :
    ¬ Law464.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_464 i
      ((@Law464.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation667_not_termDefinableFrom_Equation168 :
    ¬ Law667.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_667 i
      ((@Law667.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation870_not_termDefinableFrom_Equation168 :
    ¬ Law870.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_870 i
      ((@Law870.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation883_not_termDefinableFrom_Equation168 :
    ¬ Law883.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_883 i
      ((@Law883.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation917_not_termDefinableFrom_Equation168 :
    ¬ Law917.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_917 i
      ((@Law917.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1289_not_termDefinableFrom_Equation168 :
    ¬ Law1289.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1289 i
      ((@Law1289.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1682_not_termDefinableFrom_Equation168 :
    ¬ Law1682.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1682 i
      ((@Law1682.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1722_not_termDefinableFrom_Equation168 :
    ¬ Law1722.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1722 i
      ((@Law1722.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation168 :
    ¬ Law3272.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3272 i
      ((@Law3272.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3355_not_termDefinableFrom_Equation168 :
    ¬ Law3355.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3355 i
      ((@Law3355.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3678_not_termDefinableFrom_Equation168 :
    ¬ Law3678.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3678 i
      ((@Law3678.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation477_not_termDefinableFrom_Equation168 :
    ¬ Law477.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_477 i
      ((@Law477.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1276_not_termDefinableFrom_Equation168 :
    ¬ Law1276.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1276 i
      ((@Law1276.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3555_not_termDefinableFrom_Equation168 :
    ¬ Law3555.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3555 i
      ((@Law3555.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation118_not_termDefinableFrom_Equation168 :
    ¬ Law118.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_118 i
      ((@Law118.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation467_not_termDefinableFrom_Equation168 :
    ¬ Law467.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_467 i
      ((@Law467.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation474_not_termDefinableFrom_Equation168 :
    ¬ Law474.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_474 i
      ((@Law474.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation677_not_termDefinableFrom_Equation168 :
    ¬ Law677.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_677 i
      ((@Law677.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation704_not_termDefinableFrom_Equation168 :
    ¬ Law704.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_704 i
      ((@Law704.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1076_not_termDefinableFrom_Equation168 :
    ¬ Law1076.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1076 i
      ((@Law1076.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1110_not_termDefinableFrom_Equation168 :
    ¬ Law1110.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1110 i
      ((@Law1110.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1279_not_termDefinableFrom_Equation168 :
    ¬ Law1279.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1279 i
      ((@Law1279.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1313_not_termDefinableFrom_Equation168 :
    ¬ Law1313.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1313 i
      ((@Law1313.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1489_not_termDefinableFrom_Equation168 :
    ¬ Law1489.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1489 i
      ((@Law1489.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1516_not_termDefinableFrom_Equation168 :
    ¬ Law1516.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1516 i
      ((@Law1516.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1692_not_termDefinableFrom_Equation168 :
    ¬ Law1692.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1692 i
      ((@Law1692.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation501_not_termDefinableFrom_Equation168 :
    ¬ Law501.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_501 i
      ((@Law501.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation670_not_termDefinableFrom_Equation168 :
    ¬ Law670.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_670 i
      ((@Law670.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation907_not_termDefinableFrom_Equation168 :
    ¬ Law907.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_907 i
      ((@Law907.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation1286_not_termDefinableFrom_Equation168 :
    ¬ Law1286.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_1286 i
      ((@Law1286.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation3675_not_termDefinableFrom_Equation168 :
    ¬ Law3675.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_3675 i
      ((@Law3675.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

theorem Equation4443_not_termDefinableFrom_Equation168 :
    ¬ Law4443.TermDefinableFrom Law168 :=
  not_termDefinableFrom_of_clone Magma.negCert2
    ((@Law168.models_iff (Fin 4) Magma.negCert2).mpr negCert2_satisfies_168)
    Magma.negCert2_isCloneFamily fun i h ↦ negCert2_refutes_4443 i
      ((@Law4443.models_iff (Fin 4) (Magma.negCert2Clone i)).mp h)

/-! ### `Magma.negCert3` -/

theorem negCert3_satisfies_887 : @Equation887 (Fin 8) Magma.negCert3 := by decide!

theorem negCert3_refutes_464 : ∀ i, ¬ @Equation464 (Fin 8) (Magma.negCert3Clone i) := by
  decide!
theorem negCert3_refutes_504 : ∀ i, ¬ @Equation504 (Fin 8) (Magma.negCert3Clone i) := by
  decide!
theorem negCert3_refutes_511 : ∀ i, ¬ @Equation511 (Fin 8) (Magma.negCert3Clone i) := by
  decide!
theorem negCert3_refutes_1117 : ∀ i, ¬ @Equation1117 (Fin 8) (Magma.negCert3Clone i) := by
  decide!
theorem negCert3_refutes_1289 : ∀ i, ¬ @Equation1289 (Fin 8) (Magma.negCert3Clone i) := by
  decide!
theorem negCert3_refutes_1479 : ∀ i, ¬ @Equation1479 (Fin 8) (Magma.negCert3Clone i) := by
  decide!
theorem negCert3_refutes_1722 : ∀ i, ¬ @Equation1722 (Fin 8) (Magma.negCert3Clone i) := by
  decide!

theorem Equation504_not_termDefinableFrom_Equation887 :
    ¬ Law504.TermDefinableFrom Law887 :=
  not_termDefinableFrom_of_clone Magma.negCert3
    ((@Law887.models_iff (Fin 8) Magma.negCert3).mpr negCert3_satisfies_887)
    Magma.negCert3_isCloneFamily fun i h ↦ negCert3_refutes_504 i
      ((@Law504.models_iff (Fin 8) (Magma.negCert3Clone i)).mp h)

theorem Equation511_not_termDefinableFrom_Equation887 :
    ¬ Law511.TermDefinableFrom Law887 :=
  not_termDefinableFrom_of_clone Magma.negCert3
    ((@Law887.models_iff (Fin 8) Magma.negCert3).mpr negCert3_satisfies_887)
    Magma.negCert3_isCloneFamily fun i h ↦ negCert3_refutes_511 i
      ((@Law511.models_iff (Fin 8) (Magma.negCert3Clone i)).mp h)

theorem Equation1479_not_termDefinableFrom_Equation887 :
    ¬ Law1479.TermDefinableFrom Law887 :=
  not_termDefinableFrom_of_clone Magma.negCert3
    ((@Law887.models_iff (Fin 8) Magma.negCert3).mpr negCert3_satisfies_887)
    Magma.negCert3_isCloneFamily fun i h ↦ negCert3_refutes_1479 i
      ((@Law1479.models_iff (Fin 8) (Magma.negCert3Clone i)).mp h)

theorem Equation1722_not_termDefinableFrom_Equation887 :
    ¬ Law1722.TermDefinableFrom Law887 :=
  not_termDefinableFrom_of_clone Magma.negCert3
    ((@Law887.models_iff (Fin 8) Magma.negCert3).mpr negCert3_satisfies_887)
    Magma.negCert3_isCloneFamily fun i h ↦ negCert3_refutes_1722 i
      ((@Law1722.models_iff (Fin 8) (Magma.negCert3Clone i)).mp h)

theorem Equation464_not_termDefinableFrom_Equation887 :
    ¬ Law464.TermDefinableFrom Law887 :=
  not_termDefinableFrom_of_clone Magma.negCert3
    ((@Law887.models_iff (Fin 8) Magma.negCert3).mpr negCert3_satisfies_887)
    Magma.negCert3_isCloneFamily fun i h ↦ negCert3_refutes_464 i
      ((@Law464.models_iff (Fin 8) (Magma.negCert3Clone i)).mp h)

theorem Equation1289_not_termDefinableFrom_Equation887 :
    ¬ Law1289.TermDefinableFrom Law887 :=
  not_termDefinableFrom_of_clone Magma.negCert3
    ((@Law887.models_iff (Fin 8) Magma.negCert3).mpr negCert3_satisfies_887)
    Magma.negCert3_isCloneFamily fun i h ↦ negCert3_refutes_1289 i
      ((@Law1289.models_iff (Fin 8) (Magma.negCert3Clone i)).mp h)

theorem Equation1117_not_termDefinableFrom_Equation887 :
    ¬ Law1117.TermDefinableFrom Law887 :=
  not_termDefinableFrom_of_clone Magma.negCert3
    ((@Law887.models_iff (Fin 8) Magma.negCert3).mpr negCert3_satisfies_887)
    Magma.negCert3_isCloneFamily fun i h ↦ negCert3_refutes_1117 i
      ((@Law1117.models_iff (Fin 8) (Magma.negCert3Clone i)).mp h)

/-! ### `Magma.negCert4` -/

theorem negCert4_satisfies_895 : @Equation895 (Fin 2) Magma.negCert4 := by decide!

theorem negCert4_refutes_1482 : ∀ i, ¬ @Equation1482 (Fin 2) (Magma.negCert4Clone i) := by
  decide!

theorem Equation1482_not_termDefinableFrom_Equation895 :
    ¬ Law1482.TermDefinableFrom Law895 :=
  not_termDefinableFrom_of_clone Magma.negCert4
    ((@Law895.models_iff (Fin 2) Magma.negCert4).mpr negCert4_satisfies_895)
    Magma.negCert4_isCloneFamily fun i h ↦ negCert4_refutes_1482 i
      ((@Law1482.models_iff (Fin 2) (Magma.negCert4Clone i)).mp h)

/-! ### `Magma.negCert5` -/

theorem negCert5_satisfies_543 : @Equation543 (Fin 3) Magma.negCert5 := by decide!

theorem negCert5_refutes_1523 : ∀ i, ¬ @Equation1523 (Fin 3) (Magma.negCert5Clone i) := by
  decide!

theorem Equation1523_not_termDefinableFrom_Equation543 :
    ¬ Law1523.TermDefinableFrom Law543 :=
  not_termDefinableFrom_of_clone Magma.negCert5
    ((@Law543.models_iff (Fin 3) Magma.negCert5).mpr negCert5_satisfies_543)
    Magma.negCert5_isCloneFamily fun i h ↦ negCert5_refutes_1523 i
      ((@Law1523.models_iff (Fin 3) (Magma.negCert5Clone i)).mp h)

/-! ### `Magma.negCert6` -/

theorem negCert6_satisfies_4293 : @Equation4293 (Fin 2) Magma.negCert6 := by decide!
theorem negCert6_satisfies_4364 : @Equation4364 (Fin 2) Magma.negCert6 := by decide!
theorem negCert6_satisfies_4541 : @Equation4541 (Fin 2) Magma.negCert6 := by decide!

theorem negCert6_refutes_1519 : ∀ i, ¬ @Equation1519 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3269 : ∀ i, ¬ @Equation3269 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3272 : ∀ i, ¬ @Equation3272 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3279 : ∀ i, ¬ @Equation3279 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3364 : ∀ i, ¬ @Equation3364 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3472 : ∀ i, ¬ @Equation3472 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3475 : ∀ i, ¬ @Equation3475 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3482 : ∀ i, ¬ @Equation3482 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3607 : ∀ i, ¬ @Equation3607 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3675 : ∀ i, ¬ @Equation3675 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_3678 : ∀ i, ¬ @Equation3678 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_4273 : ∀ i, ¬ @Equation4273 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_4413 : ∀ i, ¬ @Equation4413 (Fin 2) (Magma.negCert6Clone i) := by
  decide!
theorem negCert6_refutes_4415 : ∀ i, ¬ @Equation4415 (Fin 2) (Magma.negCert6Clone i) := by
  decide!

theorem Equation4273_not_termDefinableFrom_Equation4364 :
    ¬ Law4273.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_4273 i
      ((@Law4273.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation4273_not_termDefinableFrom_Equation4541 :
    ¬ Law4273.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_4273 i
      ((@Law4273.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation4273_not_termDefinableFrom_Equation4293 :
    ¬ Law4273.TermDefinableFrom Law4293 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4293.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4293)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_4273 i
      ((@Law4273.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3364_not_termDefinableFrom_Equation4364 :
    ¬ Law3364.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3364 i
      ((@Law3364.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3472_not_termDefinableFrom_Equation4364 :
    ¬ Law3472.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3472 i
      ((@Law3472.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3364_not_termDefinableFrom_Equation4541 :
    ¬ Law3364.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3364 i
      ((@Law3364.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3472_not_termDefinableFrom_Equation4293 :
    ¬ Law3472.TermDefinableFrom Law4293 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4293.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4293)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3472 i
      ((@Law3472.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3472_not_termDefinableFrom_Equation4541 :
    ¬ Law3472.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3472 i
      ((@Law3472.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation1519_not_termDefinableFrom_Equation4293 :
    ¬ Law1519.TermDefinableFrom Law4293 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4293.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4293)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_1519 i
      ((@Law1519.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation1519_not_termDefinableFrom_Equation4364 :
    ¬ Law1519.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_1519 i
      ((@Law1519.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation4364 :
    ¬ Law3269.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3269 i
      ((@Law3269.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4293 :
    ¬ Law3272.TermDefinableFrom Law4293 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4293.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4293)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3272 i
      ((@Law3272.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4364 :
    ¬ Law3272.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3272 i
      ((@Law3272.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation4364 :
    ¬ Law3279.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3279 i
      ((@Law3279.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation4364 :
    ¬ Law3475.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3475 i
      ((@Law3475.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation4364 :
    ¬ Law3482.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3482 i
      ((@Law3482.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3607_not_termDefinableFrom_Equation4364 :
    ¬ Law3607.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3607 i
      ((@Law3607.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3678_not_termDefinableFrom_Equation4293 :
    ¬ Law3678.TermDefinableFrom Law4293 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4293.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4293)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3678 i
      ((@Law3678.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3678_not_termDefinableFrom_Equation4364 :
    ¬ Law3678.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3678 i
      ((@Law3678.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation1519_not_termDefinableFrom_Equation4541 :
    ¬ Law1519.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_1519 i
      ((@Law1519.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation4541 :
    ¬ Law3269.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3269 i
      ((@Law3269.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3272_not_termDefinableFrom_Equation4541 :
    ¬ Law3272.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3272 i
      ((@Law3272.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation4541 :
    ¬ Law3279.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3279 i
      ((@Law3279.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation4541 :
    ¬ Law3475.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3475 i
      ((@Law3475.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation4541 :
    ¬ Law3482.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3482 i
      ((@Law3482.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3607_not_termDefinableFrom_Equation4541 :
    ¬ Law3607.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3607 i
      ((@Law3607.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3675_not_termDefinableFrom_Equation4364 :
    ¬ Law3675.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3675 i
      ((@Law3675.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3678_not_termDefinableFrom_Equation4541 :
    ¬ Law3678.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3678 i
      ((@Law3678.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation4413_not_termDefinableFrom_Equation4364 :
    ¬ Law4413.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_4413 i
      ((@Law4413.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation4415_not_termDefinableFrom_Equation4364 :
    ¬ Law4415.TermDefinableFrom Law4364 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4364.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4364)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_4415 i
      ((@Law4415.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation3675_not_termDefinableFrom_Equation4541 :
    ¬ Law3675.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_3675 i
      ((@Law3675.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation4413_not_termDefinableFrom_Equation4541 :
    ¬ Law4413.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_4413 i
      ((@Law4413.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

theorem Equation4415_not_termDefinableFrom_Equation4541 :
    ¬ Law4415.TermDefinableFrom Law4541 :=
  not_termDefinableFrom_of_clone Magma.negCert6
    ((@Law4541.models_iff (Fin 2) Magma.negCert6).mpr negCert6_satisfies_4541)
    Magma.negCert6_isCloneFamily fun i h ↦ negCert6_refutes_4415 i
      ((@Law4415.models_iff (Fin 2) (Magma.negCert6Clone i)).mp h)

/-! ### `Magma.negCert7` -/

theorem negCert7_satisfies_492 : @Equation492 (Fin 9) Magma.negCert7 := by decide!

theorem negCert7_refutes_3678 : ∀ i, ¬ @Equation3678 (Fin 9) (Magma.negCert7Clone i) := by
  decide!

theorem Equation3678_not_termDefinableFrom_Equation492 :
    ¬ Law3678.TermDefinableFrom Law492 :=
  not_termDefinableFrom_of_clone Magma.negCert7
    ((@Law492.models_iff (Fin 9) Magma.negCert7).mpr negCert7_satisfies_492)
    Magma.negCert7_isCloneFamily fun i h ↦ negCert7_refutes_3678 i
      ((@Law3678.models_iff (Fin 9) (Magma.negCert7Clone i)).mp h)

/-! ### `Magma.negCert8` -/

theorem negCert8_satisfies_2700 : @Equation2700 (Fin 19) Magma.negCert8 := by decide!

theorem negCert8_refutes_1479 : ∀ i, ¬ @Equation1479 (Fin 19) (Magma.negCert8Clone i) := by
  native_decide
theorem negCert8_refutes_3355 : ∀ i, ¬ @Equation3355 (Fin 19) (Magma.negCert8Clone i) := by
  native_decide

theorem Equation3355_not_termDefinableFrom_Equation2700 :
    ¬ Law3355.TermDefinableFrom Law2700 :=
  not_termDefinableFrom_of_clone Magma.negCert8
    ((@Law2700.models_iff (Fin 19) Magma.negCert8).mpr negCert8_satisfies_2700)
    Magma.negCert8_isCloneFamily fun i h ↦ negCert8_refutes_3355 i
      ((@Law3355.models_iff (Fin 19) (Magma.negCert8Clone i)).mp h)

theorem Equation1479_not_termDefinableFrom_Equation2700 :
    ¬ Law1479.TermDefinableFrom Law2700 :=
  not_termDefinableFrom_of_clone Magma.negCert8
    ((@Law2700.models_iff (Fin 19) Magma.negCert8).mpr negCert8_satisfies_2700)
    Magma.negCert8_isCloneFamily fun i h ↦ negCert8_refutes_1479 i
      ((@Law1479.models_iff (Fin 19) (Magma.negCert8Clone i)).mp h)

/-! ### `Magma.negCert9` -/

theorem negCert9_satisfies_714 : @Equation714 (Fin 16) Magma.negCert9 := by decide!
theorem negCert9_satisfies_1313 : @Equation1313 (Fin 16) Magma.negCert9 := by decide!
theorem negCert9_satisfies_2531 : @Equation2531 (Fin 16) Magma.negCert9 := by decide!
theorem negCert9_satisfies_2910 : @Equation2910 (Fin 16) Magma.negCert9 := by decide!
theorem negCert9_satisfies_3113 : @Equation3113 (Fin 16) Magma.negCert9 := by decide!

theorem negCert9_refutes_73 : ∀ i, ¬ @Equation73 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_118 : ∀ i, ¬ @Equation118 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_167 : ∀ i, ¬ @Equation167 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_467 : ∀ i, ¬ @Equation467 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_504 : ∀ i, ¬ @Equation504 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_667 : ∀ i, ¬ @Equation667 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_704 : ∀ i, ¬ @Equation704 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_870 : ∀ i, ¬ @Equation870 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_883 : ∀ i, ¬ @Equation883 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_917 : ∀ i, ¬ @Equation917 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1086 : ∀ i, ¬ @Equation1086 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1110 : ∀ i, ¬ @Equation1110 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1279 : ∀ i, ¬ @Equation1279 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1482 : ∀ i, ¬ @Equation1482 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1489 : ∀ i, ¬ @Equation1489 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1516 : ∀ i, ¬ @Equation1516 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1526 : ∀ i, ¬ @Equation1526 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1682 : ∀ i, ¬ @Equation1682 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1685 : ∀ i, ¬ @Equation1685 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1692 : ∀ i, ¬ @Equation1692 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_1722 : ∀ i, ¬ @Equation1722 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3269 : ∀ i, ¬ @Equation3269 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3279 : ∀ i, ¬ @Equation3279 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3342 : ∀ i, ¬ @Equation3342 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3345 : ∀ i, ¬ @Equation3345 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3475 : ∀ i, ¬ @Equation3475 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3482 : ∀ i, ¬ @Equation3482 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3545 : ∀ i, ¬ @Equation3545 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3548 : ∀ i, ¬ @Equation3548 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3607 : ∀ i, ¬ @Equation3607 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_3675 : ∀ i, ¬ @Equation3675 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_4405 : ∀ i, ¬ @Equation4405 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_4443 : ∀ i, ¬ @Equation4443 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide
theorem negCert9_refutes_4482 : ∀ i, ¬ @Equation4482 (Fin 16) (Magma.negCert9Clone i) := by
  native_decide

theorem Equation4482_not_termDefinableFrom_Equation714 :
    ¬ Law4482.TermDefinableFrom Law714 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law714.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_714)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4482 i
      ((@Law4482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4482_not_termDefinableFrom_Equation1313 :
    ¬ Law4482.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law1313.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_1313)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4482 i
      ((@Law4482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4482_not_termDefinableFrom_Equation2531 :
    ¬ Law4482.TermDefinableFrom Law2531 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2531.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2531)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4482 i
      ((@Law4482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4482_not_termDefinableFrom_Equation2910 :
    ¬ Law4482.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4482 i
      ((@Law4482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation504_not_termDefinableFrom_Equation2910 :
    ¬ Law504.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_504 i
      ((@Law504.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4482_not_termDefinableFrom_Equation3113 :
    ¬ Law4482.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4482 i
      ((@Law4482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation714 :
    ¬ Law3342.TermDefinableFrom Law714 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law714.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_714)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3342 i
      ((@Law3342.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation714 :
    ¬ Law3545.TermDefinableFrom Law714 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law714.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_714)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3545 i
      ((@Law3545.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation73_not_termDefinableFrom_Equation2910 :
    ¬ Law73.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_73 i
      ((@Law73.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation73_not_termDefinableFrom_Equation3113 :
    ¬ Law73.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_73 i
      ((@Law73.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation504_not_termDefinableFrom_Equation3113 :
    ¬ Law504.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_504 i
      ((@Law504.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1086_not_termDefinableFrom_Equation2910 :
    ¬ Law1086.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1086 i
      ((@Law1086.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1086_not_termDefinableFrom_Equation3113 :
    ¬ Law1086.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1086 i
      ((@Law1086.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1526_not_termDefinableFrom_Equation2910 :
    ¬ Law1526.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1526 i
      ((@Law1526.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1685_not_termDefinableFrom_Equation2910 :
    ¬ Law1685.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1685 i
      ((@Law1685.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1685_not_termDefinableFrom_Equation3113 :
    ¬ Law1685.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1685 i
      ((@Law1685.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4405_not_termDefinableFrom_Equation714 :
    ¬ Law4405.TermDefinableFrom Law714 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law714.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_714)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4405 i
      ((@Law4405.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation118_not_termDefinableFrom_Equation2910 :
    ¬ Law118.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_118 i
      ((@Law118.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation118_not_termDefinableFrom_Equation3113 :
    ¬ Law118.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_118 i
      ((@Law118.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation467_not_termDefinableFrom_Equation2910 :
    ¬ Law467.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_467 i
      ((@Law467.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation667_not_termDefinableFrom_Equation2910 :
    ¬ Law667.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_667 i
      ((@Law667.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation704_not_termDefinableFrom_Equation2910 :
    ¬ Law704.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_704 i
      ((@Law704.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation870_not_termDefinableFrom_Equation2910 :
    ¬ Law870.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_870 i
      ((@Law870.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation870_not_termDefinableFrom_Equation3113 :
    ¬ Law870.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_870 i
      ((@Law870.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation883_not_termDefinableFrom_Equation2910 :
    ¬ Law883.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_883 i
      ((@Law883.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation917_not_termDefinableFrom_Equation2910 :
    ¬ Law917.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_917 i
      ((@Law917.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation917_not_termDefinableFrom_Equation3113 :
    ¬ Law917.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_917 i
      ((@Law917.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1110_not_termDefinableFrom_Equation2910 :
    ¬ Law1110.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1110 i
      ((@Law1110.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1279_not_termDefinableFrom_Equation2910 :
    ¬ Law1279.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1279 i
      ((@Law1279.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1482_not_termDefinableFrom_Equation1313 :
    ¬ Law1482.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law1313.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_1313)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1482 i
      ((@Law1482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1482_not_termDefinableFrom_Equation2531 :
    ¬ Law1482.TermDefinableFrom Law2531 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2531.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2531)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1482 i
      ((@Law1482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1482_not_termDefinableFrom_Equation2910 :
    ¬ Law1482.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1482 i
      ((@Law1482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1482_not_termDefinableFrom_Equation3113 :
    ¬ Law1482.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1482 i
      ((@Law1482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1489_not_termDefinableFrom_Equation2910 :
    ¬ Law1489.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1489 i
      ((@Law1489.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1516_not_termDefinableFrom_Equation2910 :
    ¬ Law1516.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1516 i
      ((@Law1516.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1682_not_termDefinableFrom_Equation1313 :
    ¬ Law1682.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law1313.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_1313)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1682 i
      ((@Law1682.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1682_not_termDefinableFrom_Equation2531 :
    ¬ Law1682.TermDefinableFrom Law2531 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2531.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2531)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1682 i
      ((@Law1682.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1682_not_termDefinableFrom_Equation2910 :
    ¬ Law1682.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1682 i
      ((@Law1682.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1692_not_termDefinableFrom_Equation2910 :
    ¬ Law1692.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1692 i
      ((@Law1692.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1692_not_termDefinableFrom_Equation3113 :
    ¬ Law1692.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1692 i
      ((@Law1692.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1722_not_termDefinableFrom_Equation2910 :
    ¬ Law1722.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1722 i
      ((@Law1722.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation1722_not_termDefinableFrom_Equation3113 :
    ¬ Law1722.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_1722 i
      ((@Law1722.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation2910 :
    ¬ Law3269.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3269 i
      ((@Law3269.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation3113 :
    ¬ Law3269.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3269 i
      ((@Law3269.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation2910 :
    ¬ Law3279.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3279 i
      ((@Law3279.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation3113 :
    ¬ Law3279.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3279 i
      ((@Law3279.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation1313 :
    ¬ Law3342.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law1313.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_1313)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3342 i
      ((@Law3342.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation2531 :
    ¬ Law3342.TermDefinableFrom Law2531 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2531.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2531)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3342 i
      ((@Law3342.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation2910 :
    ¬ Law3342.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3342 i
      ((@Law3342.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation3113 :
    ¬ Law3342.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3342 i
      ((@Law3342.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation2910 :
    ¬ Law3345.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3345 i
      ((@Law3345.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation3113 :
    ¬ Law3345.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3345 i
      ((@Law3345.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation2910 :
    ¬ Law3475.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3475 i
      ((@Law3475.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation3113 :
    ¬ Law3475.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3475 i
      ((@Law3475.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation2910 :
    ¬ Law3482.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3482 i
      ((@Law3482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation3113 :
    ¬ Law3482.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3482 i
      ((@Law3482.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation1313 :
    ¬ Law3545.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law1313.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_1313)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3545 i
      ((@Law3545.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation2531 :
    ¬ Law3545.TermDefinableFrom Law2531 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2531.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2531)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3545 i
      ((@Law3545.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation2910 :
    ¬ Law3545.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3545 i
      ((@Law3545.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation3113 :
    ¬ Law3545.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3545 i
      ((@Law3545.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation2910 :
    ¬ Law3548.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3548 i
      ((@Law3548.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation3113 :
    ¬ Law3548.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3548 i
      ((@Law3548.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3607_not_termDefinableFrom_Equation2910 :
    ¬ Law3607.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3607 i
      ((@Law3607.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3607_not_termDefinableFrom_Equation3113 :
    ¬ Law3607.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3607 i
      ((@Law3607.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation167_not_termDefinableFrom_Equation1313 :
    ¬ Law167.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law1313.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_1313)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_167 i
      ((@Law167.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation167_not_termDefinableFrom_Equation2531 :
    ¬ Law167.TermDefinableFrom Law2531 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2531.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2531)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_167 i
      ((@Law167.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation167_not_termDefinableFrom_Equation2910 :
    ¬ Law167.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_167 i
      ((@Law167.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3675_not_termDefinableFrom_Equation1313 :
    ¬ Law3675.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law1313.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_1313)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3675 i
      ((@Law3675.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3675_not_termDefinableFrom_Equation2531 :
    ¬ Law3675.TermDefinableFrom Law2531 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2531.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2531)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3675 i
      ((@Law3675.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3675_not_termDefinableFrom_Equation2910 :
    ¬ Law3675.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3675 i
      ((@Law3675.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation3675_not_termDefinableFrom_Equation3113 :
    ¬ Law3675.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_3675 i
      ((@Law3675.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4405_not_termDefinableFrom_Equation1313 :
    ¬ Law4405.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law1313.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_1313)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4405 i
      ((@Law4405.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4405_not_termDefinableFrom_Equation2531 :
    ¬ Law4405.TermDefinableFrom Law2531 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2531.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2531)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4405 i
      ((@Law4405.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4405_not_termDefinableFrom_Equation2910 :
    ¬ Law4405.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4405 i
      ((@Law4405.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4405_not_termDefinableFrom_Equation3113 :
    ¬ Law4405.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4405 i
      ((@Law4405.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4443_not_termDefinableFrom_Equation1313 :
    ¬ Law4443.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law1313.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_1313)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4443 i
      ((@Law4443.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4443_not_termDefinableFrom_Equation2531 :
    ¬ Law4443.TermDefinableFrom Law2531 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2531.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2531)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4443 i
      ((@Law4443.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4443_not_termDefinableFrom_Equation2910 :
    ¬ Law4443.TermDefinableFrom Law2910 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law2910.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_2910)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4443 i
      ((@Law4443.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

theorem Equation4443_not_termDefinableFrom_Equation3113 :
    ¬ Law4443.TermDefinableFrom Law3113 :=
  not_termDefinableFrom_of_clone Magma.negCert9
    ((@Law3113.models_iff (Fin 16) Magma.negCert9).mpr negCert9_satisfies_3113)
    Magma.negCert9_isCloneFamily fun i h ↦ negCert9_refutes_4443 i
      ((@Law4443.models_iff (Fin 16) (Magma.negCert9Clone i)).mp h)

/-! ### `Magma.negCert10` -/

theorem negCert10_satisfies_1496 : @Equation1496 (Fin 5) Magma.negCert10 := by decide!

theorem negCert10_refutes_695 : ∀ i, ¬ @Equation695 (Fin 5) (Magma.negCert10Clone i) := by
  decide!

theorem Equation695_not_termDefinableFrom_Equation1496 :
    ¬ Law695.TermDefinableFrom Law1496 :=
  not_termDefinableFrom_of_clone Magma.negCert10
    ((@Law1496.models_iff (Fin 5) Magma.negCert10).mpr negCert10_satisfies_1496)
    Magma.negCert10_isCloneFamily fun i h ↦ negCert10_refutes_695 i
      ((@Law695.models_iff (Fin 5) (Magma.negCert10Clone i)).mp h)

/-! ### `Magma.negCert11` -/

theorem negCert11_satisfies_501 : @Equation501 (Fin 13) Magma.negCert11 := by decide!
theorem negCert11_satisfies_1076 : @Equation1076 (Fin 13) Magma.negCert11 := by decide!
theorem negCert11_satisfies_1083 : @Equation1083 (Fin 13) Magma.negCert11 := by decide!
theorem negCert11_satisfies_1286 : @Equation1286 (Fin 13) Magma.negCert11 := by decide!
theorem negCert11_satisfies_1313 : @Equation1313 (Fin 13) Magma.negCert11 := by decide!

theorem negCert11_refutes_73 : ∀ i, ¬ @Equation73 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_118 : ∀ i, ¬ @Equation118 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_335 : ∀ i, ¬ @Equation335 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_464 : ∀ i, ¬ @Equation464 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_467 : ∀ i, ¬ @Equation467 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_474 : ∀ i, ¬ @Equation474 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_504 : ∀ i, ¬ @Equation504 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_511 : ∀ i, ¬ @Equation511 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_667 : ∀ i, ¬ @Equation667 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_677 : ∀ i, ¬ @Equation677 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_704 : ∀ i, ¬ @Equation704 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_870 : ∀ i, ¬ @Equation870 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_883 : ∀ i, ¬ @Equation883 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_917 : ∀ i, ¬ @Equation917 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1086 : ∀ i, ¬ @Equation1086 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1110 : ∀ i, ¬ @Equation1110 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1117 : ∀ i, ¬ @Equation1117 (Fin 13) (Magma.negCert11Clone i) := by
  native_decide
theorem negCert11_refutes_1279 : ∀ i, ¬ @Equation1279 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1289 : ∀ i, ¬ @Equation1289 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1489 : ∀ i, ¬ @Equation1489 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1516 : ∀ i, ¬ @Equation1516 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1526 : ∀ i, ¬ @Equation1526 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1685 : ∀ i, ¬ @Equation1685 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1692 : ∀ i, ¬ @Equation1692 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_1722 : ∀ i, ¬ @Equation1722 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_3269 : ∀ i, ¬ @Equation3269 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_3279 : ∀ i, ¬ @Equation3279 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_3345 : ∀ i, ¬ @Equation3345 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_3352 : ∀ i, ¬ @Equation3352 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_3475 : ∀ i, ¬ @Equation3475 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_3482 : ∀ i, ¬ @Equation3482 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_3548 : ∀ i, ¬ @Equation3548 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_3558 : ∀ i, ¬ @Equation3558 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_3748 : ∀ i, ¬ @Equation3748 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_4290 : ∀ i, ¬ @Equation4290 (Fin 13) (Magma.negCert11Clone i) := by
  decide!
theorem negCert11_refutes_4408 : ∀ i, ¬ @Equation4408 (Fin 13) (Magma.negCert11Clone i) := by
  decide!

theorem Equation4290_not_termDefinableFrom_Equation1076 :
    ¬ Law4290.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_4290 i
      ((@Law4290.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation4290_not_termDefinableFrom_Equation1313 :
    ¬ Law4290.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_4290 i
      ((@Law4290.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation4290_not_termDefinableFrom_Equation501 :
    ¬ Law4290.TermDefinableFrom Law501 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law501.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_501)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_4290 i
      ((@Law4290.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation511_not_termDefinableFrom_Equation1076 :
    ¬ Law511.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_511 i
      ((@Law511.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation511_not_termDefinableFrom_Equation1313 :
    ¬ Law511.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_511 i
      ((@Law511.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation73_not_termDefinableFrom_Equation1076 :
    ¬ Law73.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_73 i
      ((@Law73.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation73_not_termDefinableFrom_Equation1083 :
    ¬ Law73.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_73 i
      ((@Law73.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation73_not_termDefinableFrom_Equation1286 :
    ¬ Law73.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_73 i
      ((@Law73.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation73_not_termDefinableFrom_Equation1313 :
    ¬ Law73.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_73 i
      ((@Law73.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation504_not_termDefinableFrom_Equation1076 :
    ¬ Law504.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_504 i
      ((@Law504.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation504_not_termDefinableFrom_Equation1083 :
    ¬ Law504.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_504 i
      ((@Law504.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation504_not_termDefinableFrom_Equation1286 :
    ¬ Law504.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_504 i
      ((@Law504.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation504_not_termDefinableFrom_Equation1313 :
    ¬ Law504.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_504 i
      ((@Law504.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1086_not_termDefinableFrom_Equation1076 :
    ¬ Law1086.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1086 i
      ((@Law1086.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1086_not_termDefinableFrom_Equation1083 :
    ¬ Law1086.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1086 i
      ((@Law1086.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1086_not_termDefinableFrom_Equation1286 :
    ¬ Law1086.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1086 i
      ((@Law1086.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1086_not_termDefinableFrom_Equation1313 :
    ¬ Law1086.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1086 i
      ((@Law1086.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1526_not_termDefinableFrom_Equation1076 :
    ¬ Law1526.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1526 i
      ((@Law1526.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1526_not_termDefinableFrom_Equation1286 :
    ¬ Law1526.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1526 i
      ((@Law1526.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1526_not_termDefinableFrom_Equation1313 :
    ¬ Law1526.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1526 i
      ((@Law1526.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1685_not_termDefinableFrom_Equation1076 :
    ¬ Law1685.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1685 i
      ((@Law1685.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1685_not_termDefinableFrom_Equation1083 :
    ¬ Law1685.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1685 i
      ((@Law1685.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1685_not_termDefinableFrom_Equation1286 :
    ¬ Law1685.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1685 i
      ((@Law1685.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1685_not_termDefinableFrom_Equation1313 :
    ¬ Law1685.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1685 i
      ((@Law1685.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation118_not_termDefinableFrom_Equation1076 :
    ¬ Law118.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_118 i
      ((@Law118.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation118_not_termDefinableFrom_Equation1083 :
    ¬ Law118.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_118 i
      ((@Law118.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation118_not_termDefinableFrom_Equation1286 :
    ¬ Law118.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_118 i
      ((@Law118.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation118_not_termDefinableFrom_Equation1313 :
    ¬ Law118.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_118 i
      ((@Law118.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation335_not_termDefinableFrom_Equation501 :
    ¬ Law335.TermDefinableFrom Law501 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law501.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_501)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_335 i
      ((@Law335.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation335_not_termDefinableFrom_Equation1076 :
    ¬ Law335.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_335 i
      ((@Law335.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation335_not_termDefinableFrom_Equation1313 :
    ¬ Law335.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_335 i
      ((@Law335.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation464_not_termDefinableFrom_Equation1076 :
    ¬ Law464.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_464 i
      ((@Law464.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation464_not_termDefinableFrom_Equation1313 :
    ¬ Law464.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_464 i
      ((@Law464.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation467_not_termDefinableFrom_Equation1076 :
    ¬ Law467.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_467 i
      ((@Law467.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation467_not_termDefinableFrom_Equation1286 :
    ¬ Law467.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_467 i
      ((@Law467.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation467_not_termDefinableFrom_Equation1313 :
    ¬ Law467.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_467 i
      ((@Law467.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation474_not_termDefinableFrom_Equation1076 :
    ¬ Law474.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_474 i
      ((@Law474.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation474_not_termDefinableFrom_Equation1313 :
    ¬ Law474.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_474 i
      ((@Law474.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation667_not_termDefinableFrom_Equation1076 :
    ¬ Law667.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_667 i
      ((@Law667.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation667_not_termDefinableFrom_Equation1286 :
    ¬ Law667.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_667 i
      ((@Law667.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation667_not_termDefinableFrom_Equation1313 :
    ¬ Law667.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_667 i
      ((@Law667.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation677_not_termDefinableFrom_Equation1076 :
    ¬ Law677.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_677 i
      ((@Law677.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation677_not_termDefinableFrom_Equation1313 :
    ¬ Law677.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_677 i
      ((@Law677.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation704_not_termDefinableFrom_Equation1076 :
    ¬ Law704.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_704 i
      ((@Law704.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation704_not_termDefinableFrom_Equation1286 :
    ¬ Law704.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_704 i
      ((@Law704.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation704_not_termDefinableFrom_Equation1313 :
    ¬ Law704.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_704 i
      ((@Law704.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation870_not_termDefinableFrom_Equation1076 :
    ¬ Law870.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_870 i
      ((@Law870.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation870_not_termDefinableFrom_Equation1083 :
    ¬ Law870.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_870 i
      ((@Law870.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation870_not_termDefinableFrom_Equation1286 :
    ¬ Law870.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_870 i
      ((@Law870.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation870_not_termDefinableFrom_Equation1313 :
    ¬ Law870.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_870 i
      ((@Law870.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation883_not_termDefinableFrom_Equation1076 :
    ¬ Law883.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_883 i
      ((@Law883.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation883_not_termDefinableFrom_Equation1286 :
    ¬ Law883.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_883 i
      ((@Law883.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation883_not_termDefinableFrom_Equation1313 :
    ¬ Law883.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_883 i
      ((@Law883.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation917_not_termDefinableFrom_Equation1076 :
    ¬ Law917.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_917 i
      ((@Law917.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation917_not_termDefinableFrom_Equation1083 :
    ¬ Law917.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_917 i
      ((@Law917.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation917_not_termDefinableFrom_Equation1286 :
    ¬ Law917.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_917 i
      ((@Law917.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation917_not_termDefinableFrom_Equation1313 :
    ¬ Law917.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_917 i
      ((@Law917.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1110_not_termDefinableFrom_Equation1076 :
    ¬ Law1110.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1110 i
      ((@Law1110.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1110_not_termDefinableFrom_Equation1286 :
    ¬ Law1110.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1110 i
      ((@Law1110.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1110_not_termDefinableFrom_Equation1313 :
    ¬ Law1110.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1110 i
      ((@Law1110.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1117_not_termDefinableFrom_Equation501 :
    ¬ Law1117.TermDefinableFrom Law501 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law501.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_501)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1117 i
      ((@Law1117.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1279_not_termDefinableFrom_Equation1076 :
    ¬ Law1279.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1279 i
      ((@Law1279.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1279_not_termDefinableFrom_Equation1286 :
    ¬ Law1279.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1279 i
      ((@Law1279.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1279_not_termDefinableFrom_Equation1313 :
    ¬ Law1279.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1279 i
      ((@Law1279.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1289_not_termDefinableFrom_Equation1076 :
    ¬ Law1289.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1289 i
      ((@Law1289.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1289_not_termDefinableFrom_Equation1313 :
    ¬ Law1289.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1289 i
      ((@Law1289.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1489_not_termDefinableFrom_Equation1076 :
    ¬ Law1489.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1489 i
      ((@Law1489.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1489_not_termDefinableFrom_Equation1286 :
    ¬ Law1489.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1489 i
      ((@Law1489.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1489_not_termDefinableFrom_Equation1313 :
    ¬ Law1489.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1489 i
      ((@Law1489.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1516_not_termDefinableFrom_Equation1076 :
    ¬ Law1516.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1516 i
      ((@Law1516.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1516_not_termDefinableFrom_Equation1286 :
    ¬ Law1516.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1516 i
      ((@Law1516.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1516_not_termDefinableFrom_Equation1313 :
    ¬ Law1516.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1516 i
      ((@Law1516.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1692_not_termDefinableFrom_Equation1076 :
    ¬ Law1692.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1692 i
      ((@Law1692.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1692_not_termDefinableFrom_Equation1083 :
    ¬ Law1692.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1692 i
      ((@Law1692.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1692_not_termDefinableFrom_Equation1286 :
    ¬ Law1692.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1692 i
      ((@Law1692.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1692_not_termDefinableFrom_Equation1313 :
    ¬ Law1692.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1692 i
      ((@Law1692.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1722_not_termDefinableFrom_Equation1076 :
    ¬ Law1722.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1722 i
      ((@Law1722.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1722_not_termDefinableFrom_Equation1083 :
    ¬ Law1722.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1722 i
      ((@Law1722.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1722_not_termDefinableFrom_Equation1286 :
    ¬ Law1722.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1722 i
      ((@Law1722.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation1722_not_termDefinableFrom_Equation1313 :
    ¬ Law1722.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_1722 i
      ((@Law1722.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation1076 :
    ¬ Law3269.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3269 i
      ((@Law3269.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation1083 :
    ¬ Law3269.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3269 i
      ((@Law3269.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation1286 :
    ¬ Law3269.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3269 i
      ((@Law3269.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation1313 :
    ¬ Law3269.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3269 i
      ((@Law3269.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation1076 :
    ¬ Law3279.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3279 i
      ((@Law3279.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation1083 :
    ¬ Law3279.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3279 i
      ((@Law3279.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation1286 :
    ¬ Law3279.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3279 i
      ((@Law3279.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation1313 :
    ¬ Law3279.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3279 i
      ((@Law3279.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation1076 :
    ¬ Law3345.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3345 i
      ((@Law3345.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation1083 :
    ¬ Law3345.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3345 i
      ((@Law3345.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation1286 :
    ¬ Law3345.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3345 i
      ((@Law3345.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation1313 :
    ¬ Law3345.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3345 i
      ((@Law3345.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3352_not_termDefinableFrom_Equation501 :
    ¬ Law3352.TermDefinableFrom Law501 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law501.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_501)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3352 i
      ((@Law3352.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3352_not_termDefinableFrom_Equation1076 :
    ¬ Law3352.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3352 i
      ((@Law3352.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3352_not_termDefinableFrom_Equation1313 :
    ¬ Law3352.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3352 i
      ((@Law3352.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation1076 :
    ¬ Law3475.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3475 i
      ((@Law3475.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation1083 :
    ¬ Law3475.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3475 i
      ((@Law3475.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation1286 :
    ¬ Law3475.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3475 i
      ((@Law3475.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation1313 :
    ¬ Law3475.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3475 i
      ((@Law3475.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation1076 :
    ¬ Law3482.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3482 i
      ((@Law3482.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation1083 :
    ¬ Law3482.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3482 i
      ((@Law3482.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation1286 :
    ¬ Law3482.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3482 i
      ((@Law3482.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation1313 :
    ¬ Law3482.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3482 i
      ((@Law3482.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation1076 :
    ¬ Law3548.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3548 i
      ((@Law3548.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation1083 :
    ¬ Law3548.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1083.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1083)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3548 i
      ((@Law3548.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation1286 :
    ¬ Law3548.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1286.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1286)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3548 i
      ((@Law3548.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation1313 :
    ¬ Law3548.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3548 i
      ((@Law3548.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3558_not_termDefinableFrom_Equation501 :
    ¬ Law3558.TermDefinableFrom Law501 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law501.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_501)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3558 i
      ((@Law3558.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3558_not_termDefinableFrom_Equation1076 :
    ¬ Law3558.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3558 i
      ((@Law3558.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3558_not_termDefinableFrom_Equation1313 :
    ¬ Law3558.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3558 i
      ((@Law3558.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3748_not_termDefinableFrom_Equation501 :
    ¬ Law3748.TermDefinableFrom Law501 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law501.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_501)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3748 i
      ((@Law3748.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3748_not_termDefinableFrom_Equation1076 :
    ¬ Law3748.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3748 i
      ((@Law3748.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation3748_not_termDefinableFrom_Equation1313 :
    ¬ Law3748.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_3748 i
      ((@Law3748.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation4408_not_termDefinableFrom_Equation501 :
    ¬ Law4408.TermDefinableFrom Law501 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law501.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_501)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_4408 i
      ((@Law4408.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation4408_not_termDefinableFrom_Equation1076 :
    ¬ Law4408.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1076.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1076)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_4408 i
      ((@Law4408.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

theorem Equation4408_not_termDefinableFrom_Equation1313 :
    ¬ Law4408.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert11
    ((@Law1313.models_iff (Fin 13) Magma.negCert11).mpr negCert11_satisfies_1313)
    Magma.negCert11_isCloneFamily fun i h ↦ negCert11_refutes_4408 i
      ((@Law4408.models_iff (Fin 13) (Magma.negCert11Clone i)).mp h)

/-! ### `Magma.negCert12` -/

theorem negCert12_satisfies_880 : @Equation880 (Fin 5) Magma.negCert12 := by decide!

theorem negCert12_refutes_66 : ∀ i, ¬ @Equation66 (Fin 5) (Magma.negCert12Clone i) := by
  decide!
theorem negCert12_refutes_1719 : ∀ i, ¬ @Equation1719 (Fin 5) (Magma.negCert12Clone i) := by
  decide!

theorem Equation66_not_termDefinableFrom_Equation880 :
    ¬ Law66.TermDefinableFrom Law880 :=
  not_termDefinableFrom_of_clone Magma.negCert12
    ((@Law880.models_iff (Fin 5) Magma.negCert12).mpr negCert12_satisfies_880)
    Magma.negCert12_isCloneFamily fun i h ↦ negCert12_refutes_66 i
      ((@Law66.models_iff (Fin 5) (Magma.negCert12Clone i)).mp h)

theorem Equation1719_not_termDefinableFrom_Equation880 :
    ¬ Law1719.TermDefinableFrom Law880 :=
  not_termDefinableFrom_of_clone Magma.negCert12
    ((@Law880.models_iff (Fin 5) Magma.negCert12).mpr negCert12_satisfies_880)
    Magma.negCert12_isCloneFamily fun i h ↦ negCert12_refutes_1719 i
      ((@Law1719.models_iff (Fin 5) (Magma.negCert12Clone i)).mp h)

/-! ### `Magma.negCert13` -/

theorem negCert13_satisfies_464 : @Equation464 (Fin 16) Magma.negCert13 := by decide!
theorem negCert13_satisfies_670 : @Equation670 (Fin 16) Magma.negCert13 := by decide!
theorem negCert13_satisfies_1083 : @Equation1083 (Fin 16) Magma.negCert13 := by decide!
theorem negCert13_satisfies_1286 : @Equation1286 (Fin 16) Magma.negCert13 := by decide!

theorem negCert13_refutes_1479 : ∀ i, ¬ @Equation1479 (Fin 16) (Magma.negCert13Clone i) := by
  native_decide
theorem negCert13_refutes_1482 : ∀ i, ¬ @Equation1482 (Fin 16) (Magma.negCert13Clone i) := by
  native_decide
theorem negCert13_refutes_3342 : ∀ i, ¬ @Equation3342 (Fin 16) (Magma.negCert13Clone i) := by
  native_decide
theorem negCert13_refutes_3545 : ∀ i, ¬ @Equation3545 (Fin 16) (Magma.negCert13Clone i) := by
  native_decide
theorem negCert13_refutes_3555 : ∀ i, ¬ @Equation3555 (Fin 16) (Magma.negCert13Clone i) := by
  native_decide
theorem negCert13_refutes_4405 : ∀ i, ¬ @Equation4405 (Fin 16) (Magma.negCert13Clone i) := by
  native_decide
theorem negCert13_refutes_4482 : ∀ i, ¬ @Equation4482 (Fin 16) (Magma.negCert13Clone i) := by
  native_decide

theorem Equation4482_not_termDefinableFrom_Equation1083 :
    ¬ Law4482.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1083.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1083)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_4482 i
      ((@Law4482.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation4482_not_termDefinableFrom_Equation1286 :
    ¬ Law4482.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1286.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1286)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_4482 i
      ((@Law4482.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation4482_not_termDefinableFrom_Equation464 :
    ¬ Law4482.TermDefinableFrom Law464 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law464.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_464)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_4482 i
      ((@Law4482.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation1479_not_termDefinableFrom_Equation670 :
    ¬ Law1479.TermDefinableFrom Law670 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law670.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_670)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_1479 i
      ((@Law1479.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation1482_not_termDefinableFrom_Equation670 :
    ¬ Law1482.TermDefinableFrom Law670 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law670.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_670)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_1482 i
      ((@Law1482.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation464 :
    ¬ Law3342.TermDefinableFrom Law464 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law464.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_464)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_3342 i
      ((@Law3342.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation1083 :
    ¬ Law3342.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1083.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1083)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_3342 i
      ((@Law3342.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation1286 :
    ¬ Law3342.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1286.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1286)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_3342 i
      ((@Law3342.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation464 :
    ¬ Law3545.TermDefinableFrom Law464 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law464.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_464)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_3545 i
      ((@Law3545.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation1083 :
    ¬ Law3545.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1083.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1083)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_3545 i
      ((@Law3545.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation1286 :
    ¬ Law3545.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1286.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1286)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_3545 i
      ((@Law3545.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation3555_not_termDefinableFrom_Equation1083 :
    ¬ Law3555.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1083.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1083)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_3555 i
      ((@Law3555.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation3555_not_termDefinableFrom_Equation1286 :
    ¬ Law3555.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1286.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1286)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_3555 i
      ((@Law3555.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation4405_not_termDefinableFrom_Equation464 :
    ¬ Law4405.TermDefinableFrom Law464 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law464.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_464)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_4405 i
      ((@Law4405.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation4405_not_termDefinableFrom_Equation1083 :
    ¬ Law4405.TermDefinableFrom Law1083 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1083.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1083)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_4405 i
      ((@Law4405.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

theorem Equation4405_not_termDefinableFrom_Equation1286 :
    ¬ Law4405.TermDefinableFrom Law1286 :=
  not_termDefinableFrom_of_clone Magma.negCert13
    ((@Law1286.models_iff (Fin 16) Magma.negCert13).mpr negCert13_satisfies_1286)
    Magma.negCert13_isCloneFamily fun i h ↦ negCert13_refutes_4405 i
      ((@Law4405.models_iff (Fin 16) (Magma.negCert13Clone i)).mp h)

/-! ### `Magma.negCert14` -/

theorem negCert14_satisfies_1682 : @Equation1682 (Fin 13) Magma.negCert14 := by decide!
theorem negCert14_satisfies_3555 : @Equation3555 (Fin 13) Magma.negCert14 := by decide!
theorem negCert14_satisfies_3675 : @Equation3675 (Fin 13) Magma.negCert14 := by decide!
theorem negCert14_satisfies_4321 : @Equation4321 (Fin 13) Magma.negCert14 := by decide!
theorem negCert14_satisfies_4443 : @Equation4443 (Fin 13) Magma.negCert14 := by decide!

theorem negCert14_refutes_335 : ∀ i, ¬ @Equation335 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_667 : ∀ i, ¬ @Equation667 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_870 : ∀ i, ¬ @Equation870 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_883 : ∀ i, ¬ @Equation883 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_917 : ∀ i, ¬ @Equation917 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_1086 : ∀ i, ¬ @Equation1086 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_1526 : ∀ i, ¬ @Equation1526 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_3269 : ∀ i, ¬ @Equation3269 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_3279 : ∀ i, ¬ @Equation3279 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_3345 : ∀ i, ¬ @Equation3345 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_3352 : ∀ i, ¬ @Equation3352 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_3475 : ∀ i, ¬ @Equation3475 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_3482 : ∀ i, ¬ @Equation3482 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_3548 : ∀ i, ¬ @Equation3548 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_3558 : ∀ i, ¬ @Equation3558 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_3748 : ∀ i, ¬ @Equation3748 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_4290 : ∀ i, ¬ @Equation4290 (Fin 13) (Magma.negCert14Clone i) := by
  decide!
theorem negCert14_refutes_4408 : ∀ i, ¬ @Equation4408 (Fin 13) (Magma.negCert14Clone i) := by
  decide!

theorem Equation4290_not_termDefinableFrom_Equation1682 :
    ¬ Law4290.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_4290 i
      ((@Law4290.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation1086_not_termDefinableFrom_Equation1682 :
    ¬ Law1086.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_1086 i
      ((@Law1086.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation1526_not_termDefinableFrom_Equation1682 :
    ¬ Law1526.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_1526 i
      ((@Law1526.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation4290_not_termDefinableFrom_Equation3675 :
    ¬ Law4290.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_4290 i
      ((@Law4290.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation335_not_termDefinableFrom_Equation1682 :
    ¬ Law335.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_335 i
      ((@Law335.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation335_not_termDefinableFrom_Equation4321 :
    ¬ Law335.TermDefinableFrom Law4321 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4321.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4321)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_335 i
      ((@Law335.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation667_not_termDefinableFrom_Equation1682 :
    ¬ Law667.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_667 i
      ((@Law667.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation870_not_termDefinableFrom_Equation1682 :
    ¬ Law870.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_870 i
      ((@Law870.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation883_not_termDefinableFrom_Equation1682 :
    ¬ Law883.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_883 i
      ((@Law883.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation917_not_termDefinableFrom_Equation1682 :
    ¬ Law917.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_917 i
      ((@Law917.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation1682 :
    ¬ Law3269.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3269 i
      ((@Law3269.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation1682 :
    ¬ Law3279.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3279 i
      ((@Law3279.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation1682 :
    ¬ Law3345.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3345 i
      ((@Law3345.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation3555 :
    ¬ Law3345.TermDefinableFrom Law3555 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3555.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3555)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3345 i
      ((@Law3345.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation4321 :
    ¬ Law3345.TermDefinableFrom Law4321 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4321.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4321)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3345 i
      ((@Law3345.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3352_not_termDefinableFrom_Equation1682 :
    ¬ Law3352.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3352 i
      ((@Law3352.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3352_not_termDefinableFrom_Equation4321 :
    ¬ Law3352.TermDefinableFrom Law4321 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4321.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4321)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3352 i
      ((@Law3352.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation1682 :
    ¬ Law3475.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3475 i
      ((@Law3475.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation1682 :
    ¬ Law3482.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3482 i
      ((@Law3482.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation1682 :
    ¬ Law3548.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3548 i
      ((@Law3548.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation3555 :
    ¬ Law3548.TermDefinableFrom Law3555 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3555.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3555)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3548 i
      ((@Law3548.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation4321 :
    ¬ Law3548.TermDefinableFrom Law4321 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4321.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4321)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3548 i
      ((@Law3548.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3558_not_termDefinableFrom_Equation1682 :
    ¬ Law3558.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3558 i
      ((@Law3558.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3558_not_termDefinableFrom_Equation4321 :
    ¬ Law3558.TermDefinableFrom Law4321 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4321.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4321)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3558 i
      ((@Law3558.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3748_not_termDefinableFrom_Equation1682 :
    ¬ Law3748.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3748 i
      ((@Law3748.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3748_not_termDefinableFrom_Equation4321 :
    ¬ Law3748.TermDefinableFrom Law4321 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4321.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4321)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3748 i
      ((@Law3748.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation4290_not_termDefinableFrom_Equation4321 :
    ¬ Law4290.TermDefinableFrom Law4321 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4321.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4321)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_4290 i
      ((@Law4290.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation4408_not_termDefinableFrom_Equation1682 :
    ¬ Law4408.TermDefinableFrom Law1682 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law1682.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_1682)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_4408 i
      ((@Law4408.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation4408_not_termDefinableFrom_Equation4321 :
    ¬ Law4408.TermDefinableFrom Law4321 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4321.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4321)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_4408 i
      ((@Law4408.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation335_not_termDefinableFrom_Equation3675 :
    ¬ Law335.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_335 i
      ((@Law335.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation335_not_termDefinableFrom_Equation4443 :
    ¬ Law335.TermDefinableFrom Law4443 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4443.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4443)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_335 i
      ((@Law335.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3269_not_termDefinableFrom_Equation3675 :
    ¬ Law3269.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3269 i
      ((@Law3269.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3279_not_termDefinableFrom_Equation3675 :
    ¬ Law3279.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3279 i
      ((@Law3279.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation3675 :
    ¬ Law3345.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3345 i
      ((@Law3345.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3345_not_termDefinableFrom_Equation4443 :
    ¬ Law3345.TermDefinableFrom Law4443 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4443.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4443)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3345 i
      ((@Law3345.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3352_not_termDefinableFrom_Equation3675 :
    ¬ Law3352.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3352 i
      ((@Law3352.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3352_not_termDefinableFrom_Equation4443 :
    ¬ Law3352.TermDefinableFrom Law4443 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4443.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4443)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3352 i
      ((@Law3352.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3475_not_termDefinableFrom_Equation3675 :
    ¬ Law3475.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3475 i
      ((@Law3475.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3482_not_termDefinableFrom_Equation3675 :
    ¬ Law3482.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3482 i
      ((@Law3482.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation3675 :
    ¬ Law3548.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3548 i
      ((@Law3548.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3548_not_termDefinableFrom_Equation4443 :
    ¬ Law3548.TermDefinableFrom Law4443 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4443.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4443)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3548 i
      ((@Law3548.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3558_not_termDefinableFrom_Equation3675 :
    ¬ Law3558.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3558 i
      ((@Law3558.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3558_not_termDefinableFrom_Equation4443 :
    ¬ Law3558.TermDefinableFrom Law4443 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4443.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4443)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3558 i
      ((@Law3558.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3748_not_termDefinableFrom_Equation3675 :
    ¬ Law3748.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3748 i
      ((@Law3748.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation3748_not_termDefinableFrom_Equation4443 :
    ¬ Law3748.TermDefinableFrom Law4443 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4443.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4443)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_3748 i
      ((@Law3748.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation4290_not_termDefinableFrom_Equation4443 :
    ¬ Law4290.TermDefinableFrom Law4443 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4443.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4443)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_4290 i
      ((@Law4290.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation4408_not_termDefinableFrom_Equation3675 :
    ¬ Law4408.TermDefinableFrom Law3675 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law3675.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_3675)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_4408 i
      ((@Law4408.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

theorem Equation4408_not_termDefinableFrom_Equation4443 :
    ¬ Law4408.TermDefinableFrom Law4443 :=
  not_termDefinableFrom_of_clone Magma.negCert14
    ((@Law4443.models_iff (Fin 13) Magma.negCert14).mpr negCert14_satisfies_4443)
    Magma.negCert14_isCloneFamily fun i h ↦ negCert14_refutes_4408 i
      ((@Law4408.models_iff (Fin 13) (Magma.negCert14Clone i)).mp h)

/-! ### `Magma.negCert15` -/

theorem negCert15_satisfies_907 : @Equation907 (Fin 13) Magma.negCert15 := by decide!

theorem negCert15_refutes_464 : ∀ i, ¬ @Equation464 (Fin 13) (Magma.negCert15Clone i) := by
  decide!
theorem negCert15_refutes_511 : ∀ i, ¬ @Equation511 (Fin 13) (Magma.negCert15Clone i) := by
  decide!
theorem negCert15_refutes_1289 : ∀ i, ¬ @Equation1289 (Fin 13) (Magma.negCert15Clone i) := by
  decide!
theorem negCert15_refutes_3601 : ∀ i, ¬ @Equation3601 (Fin 13) (Magma.negCert15Clone i) := by
  native_decide
theorem negCert15_refutes_4305 : ∀ i, ¬ @Equation4305 (Fin 13) (Magma.negCert15Clone i) := by
  native_decide
theorem negCert15_refutes_4413 : ∀ i, ¬ @Equation4413 (Fin 13) (Magma.negCert15Clone i) := by
  native_decide
theorem negCert15_refutes_4421 : ∀ i, ¬ @Equation4421 (Fin 13) (Magma.negCert15Clone i) := by
  native_decide

theorem Equation511_not_termDefinableFrom_Equation907 :
    ¬ Law511.TermDefinableFrom Law907 :=
  not_termDefinableFrom_of_clone Magma.negCert15
    ((@Law907.models_iff (Fin 13) Magma.negCert15).mpr negCert15_satisfies_907)
    Magma.negCert15_isCloneFamily fun i h ↦ negCert15_refutes_511 i
      ((@Law511.models_iff (Fin 13) (Magma.negCert15Clone i)).mp h)

theorem Equation464_not_termDefinableFrom_Equation907 :
    ¬ Law464.TermDefinableFrom Law907 :=
  not_termDefinableFrom_of_clone Magma.negCert15
    ((@Law907.models_iff (Fin 13) Magma.negCert15).mpr negCert15_satisfies_907)
    Magma.negCert15_isCloneFamily fun i h ↦ negCert15_refutes_464 i
      ((@Law464.models_iff (Fin 13) (Magma.negCert15Clone i)).mp h)

theorem Equation1289_not_termDefinableFrom_Equation907 :
    ¬ Law1289.TermDefinableFrom Law907 :=
  not_termDefinableFrom_of_clone Magma.negCert15
    ((@Law907.models_iff (Fin 13) Magma.negCert15).mpr negCert15_satisfies_907)
    Magma.negCert15_isCloneFamily fun i h ↦ negCert15_refutes_1289 i
      ((@Law1289.models_iff (Fin 13) (Magma.negCert15Clone i)).mp h)

theorem Equation3601_not_termDefinableFrom_Equation907 :
    ¬ Law3601.TermDefinableFrom Law907 :=
  not_termDefinableFrom_of_clone Magma.negCert15
    ((@Law907.models_iff (Fin 13) Magma.negCert15).mpr negCert15_satisfies_907)
    Magma.negCert15_isCloneFamily fun i h ↦ negCert15_refutes_3601 i
      ((@Law3601.models_iff (Fin 13) (Magma.negCert15Clone i)).mp h)

theorem Equation4305_not_termDefinableFrom_Equation907 :
    ¬ Law4305.TermDefinableFrom Law907 :=
  not_termDefinableFrom_of_clone Magma.negCert15
    ((@Law907.models_iff (Fin 13) Magma.negCert15).mpr negCert15_satisfies_907)
    Magma.negCert15_isCloneFamily fun i h ↦ negCert15_refutes_4305 i
      ((@Law4305.models_iff (Fin 13) (Magma.negCert15Clone i)).mp h)

theorem Equation4421_not_termDefinableFrom_Equation907 :
    ¬ Law4421.TermDefinableFrom Law907 :=
  not_termDefinableFrom_of_clone Magma.negCert15
    ((@Law907.models_iff (Fin 13) Magma.negCert15).mpr negCert15_satisfies_907)
    Magma.negCert15_isCloneFamily fun i h ↦ negCert15_refutes_4421 i
      ((@Law4421.models_iff (Fin 13) (Magma.negCert15Clone i)).mp h)

theorem Equation4413_not_termDefinableFrom_Equation907 :
    ¬ Law4413.TermDefinableFrom Law907 :=
  not_termDefinableFrom_of_clone Magma.negCert15
    ((@Law907.models_iff (Fin 13) Magma.negCert15).mpr negCert15_satisfies_907)
    Magma.negCert15_isCloneFamily fun i h ↦ negCert15_refutes_4413 i
      ((@Law4413.models_iff (Fin 13) (Magma.negCert15Clone i)).mp h)

/-! ### `Magma.negCert16` -/

theorem negCert16_satisfies_501 : @Equation501 (Fin 5) Magma.negCert16 := by decide!

theorem negCert16_refutes_66 : ∀ i, ¬ @Equation66 (Fin 5) (Magma.negCert16Clone i) := by
  decide!

theorem Equation66_not_termDefinableFrom_Equation501 :
    ¬ Law66.TermDefinableFrom Law501 :=
  not_termDefinableFrom_of_clone Magma.negCert16
    ((@Law501.models_iff (Fin 5) Magma.negCert16).mpr negCert16_satisfies_501)
    Magma.negCert16_isCloneFamily fun i h ↦ negCert16_refutes_66 i
      ((@Law66.models_iff (Fin 5) (Magma.negCert16Clone i)).mp h)

/-! ### `Magma.negCert17` -/

theorem negCert17_satisfies_1323 : @Equation1323 (Fin 4) Magma.negCert17 := by decide!

theorem negCert17_refutes_667 : ∀ i, ¬ @Equation667 (Fin 4) (Magma.negCert17Clone i) := by
  decide!

theorem Equation667_not_termDefinableFrom_Equation1323 :
    ¬ Law667.TermDefinableFrom Law1323 :=
  not_termDefinableFrom_of_clone Magma.negCert17
    ((@Law1323.models_iff (Fin 4) Magma.negCert17).mpr negCert17_satisfies_1323)
    Magma.negCert17_isCloneFamily fun i h ↦ negCert17_refutes_667 i
      ((@Law667.models_iff (Fin 4) (Magma.negCert17Clone i)).mp h)

/-! ### `Magma.negCert18` -/

theorem negCert18_satisfies_1076 : @Equation1076 (Fin 17) Magma.negCert18 := by decide!
theorem negCert18_satisfies_2294 : @Equation2294 (Fin 17) Magma.negCert18 := by decide!
theorem negCert18_satisfies_4658 : @Equation4658 (Fin 17) Magma.negCert18 := by decide!

theorem negCert18_refutes_707 : ∀ i, ¬ @Equation707 (Fin 17) (Magma.negCert18Clone i) := by
  native_decide
theorem negCert18_refutes_1113 : ∀ i, ¬ @Equation1113 (Fin 17) (Magma.negCert18Clone i) := by
  native_decide
theorem negCert18_refutes_3555 : ∀ i, ¬ @Equation3555 (Fin 17) (Magma.negCert18Clone i) := by
  native_decide

theorem Equation707_not_termDefinableFrom_Equation1076 :
    ¬ Law707.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert18
    ((@Law1076.models_iff (Fin 17) Magma.negCert18).mpr negCert18_satisfies_1076)
    Magma.negCert18_isCloneFamily fun i h ↦ negCert18_refutes_707 i
      ((@Law707.models_iff (Fin 17) (Magma.negCert18Clone i)).mp h)

theorem Equation707_not_termDefinableFrom_Equation2294 :
    ¬ Law707.TermDefinableFrom Law2294 :=
  not_termDefinableFrom_of_clone Magma.negCert18
    ((@Law2294.models_iff (Fin 17) Magma.negCert18).mpr negCert18_satisfies_2294)
    Magma.negCert18_isCloneFamily fun i h ↦ negCert18_refutes_707 i
      ((@Law707.models_iff (Fin 17) (Magma.negCert18Clone i)).mp h)

theorem Equation1113_not_termDefinableFrom_Equation1076 :
    ¬ Law1113.TermDefinableFrom Law1076 :=
  not_termDefinableFrom_of_clone Magma.negCert18
    ((@Law1076.models_iff (Fin 17) Magma.negCert18).mpr negCert18_satisfies_1076)
    Magma.negCert18_isCloneFamily fun i h ↦ negCert18_refutes_1113 i
      ((@Law1113.models_iff (Fin 17) (Magma.negCert18Clone i)).mp h)

theorem Equation1113_not_termDefinableFrom_Equation2294 :
    ¬ Law1113.TermDefinableFrom Law2294 :=
  not_termDefinableFrom_of_clone Magma.negCert18
    ((@Law2294.models_iff (Fin 17) Magma.negCert18).mpr negCert18_satisfies_2294)
    Magma.negCert18_isCloneFamily fun i h ↦ negCert18_refutes_1113 i
      ((@Law1113.models_iff (Fin 17) (Magma.negCert18Clone i)).mp h)

theorem Equation3555_not_termDefinableFrom_Equation4658 :
    ¬ Law3555.TermDefinableFrom Law4658 :=
  not_termDefinableFrom_of_clone Magma.negCert18
    ((@Law4658.models_iff (Fin 17) Magma.negCert18).mpr negCert18_satisfies_4658)
    Magma.negCert18_isCloneFamily fun i h ↦ negCert18_refutes_3555 i
      ((@Law3555.models_iff (Fin 17) (Magma.negCert18Clone i)).mp h)

/-! ### `Magma.negCert19` -/

theorem negCert19_satisfies_3272 : @Equation3272 (Fin 9) Magma.negCert19 := by decide!

theorem negCert19_refutes_3678 : ∀ i, ¬ @Equation3678 (Fin 9) (Magma.negCert19Clone i) := by
  decide!

theorem Equation3678_not_termDefinableFrom_Equation3272 :
    ¬ Law3678.TermDefinableFrom Law3272 :=
  not_termDefinableFrom_of_clone Magma.negCert19
    ((@Law3272.models_iff (Fin 9) Magma.negCert19).mpr negCert19_satisfies_3272)
    Magma.negCert19_isCloneFamily fun i h ↦ negCert19_refutes_3678 i
      ((@Law3678.models_iff (Fin 9) (Magma.negCert19Clone i)).mp h)

/-! ### `Magma.negCert20` -/

theorem negCert20_satisfies_1313 : @Equation1313 (Fin 7) Magma.negCert20 := by decide!

theorem negCert20_refutes_1076 : ∀ i, ¬ @Equation1076 (Fin 7) (Magma.negCert20Clone i) := by
  decide!

theorem Equation1076_not_termDefinableFrom_Equation1313 :
    ¬ Law1076.TermDefinableFrom Law1313 :=
  not_termDefinableFrom_of_clone Magma.negCert20
    ((@Law1313.models_iff (Fin 7) Magma.negCert20).mpr negCert20_satisfies_1313)
    Magma.negCert20_isCloneFamily fun i h ↦ negCert20_refutes_1076 i
      ((@Law1076.models_iff (Fin 7) (Magma.negCert20Clone i)).mp h)

