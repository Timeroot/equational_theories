import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: S3 fixing a point of Fin 4

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 1024 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### S3 fixing a point of Fin 4 -/

namespace sym3

/-- The 6 permutations of `Fin 4`, and their inverses. -/
def E : Fin 6 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1]]

def Einv : Fin 6 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 3, 1, 2], ![0, 2, 3, 1], ![0, 3, 2, 1]]

/-- One ordered pair per orbit (5 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 5 → Fin 4 × Fin 4 := ![(0, 0), (0, 1), (1, 0), (1, 1), (1, 2)]

def tr : Fin 4 → Fin 4 → Fin 5 × Fin 6 := fun x y ↦
  ![![(0, 0), (1, 0), (1, 2), (1, 4)], ![(2, 0), (3, 0), (4, 0), (4, 1)], ![(2, 2), (4, 2), (3, 2), (4, 3)], ![(2, 4), (4, 4), (4, 5), (3, 4)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end sym3

/-! ### The refuted targets -/

/-- No sym3-invariant operation on `Fin 4` satisfies equation 1482. -/
theorem nosym3_Law1482 : ∀ v : Fin 5 → Fin 4,
    (∀ i, (Magma.mk (Magma.transport sym3.E sym3.tr v)).IsEndo (sym3.E i)) →
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.transport sym3.E sym3.tr v)) Law1482 := by
  simp only [Law1482.models_iff]
  native_decide

/-- No sym3-invariant operation on `Fin 4` satisfies equation 1483. -/
theorem nosym3_Law1483 : ∀ v : Fin 5 → Fin 4,
    (∀ i, (Magma.mk (Magma.transport sym3.E sym3.tr v)).IsEndo (sym3.E i)) →
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.transport sym3.E sym3.tr v)) Law1483 := by
  simp only [Law1483.models_iff]
  native_decide

/-- No sym3-invariant operation on `Fin 4` satisfies equation 1485. -/
theorem nosym3_Law1485 : ∀ v : Fin 5 → Fin 4,
    (∀ i, (Magma.mk (Magma.transport sym3.E sym3.tr v)).IsEndo (sym3.E i)) →
    ¬ @satisfies _ (Fin 4) (Magma.mk (Magma.transport sym3.E sym3.tr v)) Law1485 := by
  simp only [Law1485.models_iff]
  native_decide

/-! ### The sources -/

/-- A model of equation 40 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M40 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] x y

theorem sym3M40_models : @satisfies _ (Fin 4) sym3M40 Law40 :=
  (@Law40.models_iff (Fin 4) sym3M40).mpr (by native_decide)

theorem sym3M40_endo : ∀ i, sym3M40.IsEndo (sym3.E i) := by decide

/-- A model of equation 481 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M481 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] x y

theorem sym3M481_models : @satisfies _ (Fin 4) sym3M481 Law481 :=
  (@Law481.models_iff (Fin 4) sym3M481).mpr (by native_decide)

theorem sym3M481_endo : ∀ i, sym3M481.IsEndo (sym3.E i) := by decide

/-- A model of equation 508 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M508 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![1, 0, 2, 3], ![2, 1, 0, 3], ![3, 1, 2, 0]] x y

theorem sym3M508_models : @satisfies _ (Fin 4) sym3M508 Law508 :=
  (@Law508.models_iff (Fin 4) sym3M508).mpr (by native_decide)

theorem sym3M508_endo : ∀ i, sym3M508.IsEndo (sym3.E i) := by decide

/-- A model of equation 543 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M543 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] x y

theorem sym3M543_models : @satisfies _ (Fin 4) sym3M543 Law543 :=
  (@Law543.models_iff (Fin 4) sym3M543).mpr (by native_decide)

theorem sym3M543_endo : ∀ i, sym3M543.IsEndo (sym3.E i) := by decide

/-- A model of equation 546 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M546 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] x y

theorem sym3M546_models : @satisfies _ (Fin 4) sym3M546 Law546 :=
  (@Law546.models_iff (Fin 4) sym3M546).mpr (by native_decide)

theorem sym3M546_endo : ∀ i, sym3M546.IsEndo (sym3.E i) := by decide

/-- A model of equation 695 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M695 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] x y

theorem sym3M695_models : @satisfies _ (Fin 4) sym3M695 Law695 :=
  (@Law695.models_iff (Fin 4) sym3M695).mpr (by native_decide)

theorem sym3M695_endo : ∀ i, sym3M695.IsEndo (sym3.E i) := by decide

/-- A model of equation 895 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M895 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] x y

theorem sym3M895_models : @satisfies _ (Fin 4) sym3M895 Law895 :=
  (@Law895.models_iff (Fin 4) sym3M895).mpr (by native_decide)

theorem sym3M895_endo : ∀ i, sym3M895.IsEndo (sym3.E i) := by decide

/-- A model of equation 978 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M978 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] x y

theorem sym3M978_models : @satisfies _ (Fin 4) sym3M978 Law978 :=
  (@Law978.models_iff (Fin 4) sym3M978).mpr (by native_decide)

theorem sym3M978_endo : ∀ i, sym3M978.IsEndo (sym3.E i) := by decide

/-- A model of equation 1523 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M1523 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![1, 0, 0, 0], ![2, 0, 0, 0], ![3, 0, 0, 0]] x y

theorem sym3M1523_models : @satisfies _ (Fin 4) sym3M1523 Law1523 :=
  (@Law1523.models_iff (Fin 4) sym3M1523).mpr (by native_decide)

theorem sym3M1523_endo : ∀ i, sym3M1523.IsEndo (sym3.E i) := by decide

/-- A model of equation 1682 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M1682 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] x y

theorem sym3M1682_models : @satisfies _ (Fin 4) sym3M1682 Law1682 :=
  (@Law1682.models_iff (Fin 4) sym3M1682).mpr (by native_decide)

theorem sym3M1682_endo : ∀ i, sym3M1682.IsEndo (sym3.E i) := by decide

/-- A model of equation 3607 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M3607 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] x y

theorem sym3M3607_models : @satisfies _ (Fin 4) sym3M3607 Law3607 :=
  (@Law3607.models_iff (Fin 4) sym3M3607).mpr (by native_decide)

theorem sym3M3607_endo : ∀ i, sym3M3607.IsEndo (sym3.E i) := by decide

/-- A model of equation 3675 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M3675 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] x y

theorem sym3M3675_models : @satisfies _ (Fin 4) sym3M3675 Law3675 :=
  (@Law3675.models_iff (Fin 4) sym3M3675).mpr (by native_decide)

theorem sym3M3675_endo : ∀ i, sym3M3675.IsEndo (sym3.E i) := by decide

/-- A model of equation 4364 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M4364 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] x y

theorem sym3M4364_models : @satisfies _ (Fin 4) sym3M4364 Law4364 :=
  (@Law4364.models_iff (Fin 4) sym3M4364).mpr (by native_decide)

theorem sym3M4364_endo : ∀ i, sym3M4364.IsEndo (sym3.E i) := by decide

/-- A model of equation 4541 on `Fin 4` invariant under sym3. -/
@[reducible]
def sym3M4541 : Magma (Fin 4) := Magma.mk fun x y ↦ ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] x y

theorem sym3M4541_models : @satisfies _ (Fin 4) sym3M4541 Law4541 :=
  (@Law4541.models_iff (Fin 4) sym3M4541).mpr (by native_decide)

theorem sym3M4541_endo : ∀ i, sym3M4541.IsEndo (sym3.E i) := by decide

/-! ### The refutations -- 20 cells -/

theorem Equation1482_not_definableFrom_Equation40 :
    ¬ Law1482.DefinableFrom Law40 :=
  not_definableFrom_transport (sym3M40 : Magma (Fin 4)) sym3M40_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M40_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation481 :
    ¬ Law1482.DefinableFrom Law481 :=
  not_definableFrom_transport (sym3M481 : Magma (Fin 4)) sym3M481_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M481_endo sym3.htr
    nosym3_Law1482

theorem Equation1483_not_definableFrom_Equation481 :
    ¬ Law1483.DefinableFrom Law481 :=
  not_definableFrom_transport (sym3M481 : Magma (Fin 4)) sym3M481_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M481_endo sym3.htr
    nosym3_Law1483

theorem Equation1485_not_definableFrom_Equation481 :
    ¬ Law1485.DefinableFrom Law481 :=
  not_definableFrom_transport (sym3M481 : Magma (Fin 4)) sym3M481_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M481_endo sym3.htr
    nosym3_Law1485

theorem Equation1482_not_definableFrom_Equation508 :
    ¬ Law1482.DefinableFrom Law508 :=
  not_definableFrom_transport (sym3M508 : Magma (Fin 4)) sym3M508_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M508_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation543 :
    ¬ Law1482.DefinableFrom Law543 :=
  not_definableFrom_transport (sym3M543 : Magma (Fin 4)) sym3M543_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M543_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation546 :
    ¬ Law1482.DefinableFrom Law546 :=
  not_definableFrom_transport (sym3M546 : Magma (Fin 4)) sym3M546_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M546_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation695 :
    ¬ Law1482.DefinableFrom Law695 :=
  not_definableFrom_transport (sym3M695 : Magma (Fin 4)) sym3M695_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M695_endo sym3.htr
    nosym3_Law1482

theorem Equation1483_not_definableFrom_Equation695 :
    ¬ Law1483.DefinableFrom Law695 :=
  not_definableFrom_transport (sym3M695 : Magma (Fin 4)) sym3M695_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M695_endo sym3.htr
    nosym3_Law1483

theorem Equation1485_not_definableFrom_Equation695 :
    ¬ Law1485.DefinableFrom Law695 :=
  not_definableFrom_transport (sym3M695 : Magma (Fin 4)) sym3M695_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M695_endo sym3.htr
    nosym3_Law1485

theorem Equation1482_not_definableFrom_Equation895 :
    ¬ Law1482.DefinableFrom Law895 :=
  not_definableFrom_transport (sym3M895 : Magma (Fin 4)) sym3M895_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M895_endo sym3.htr
    nosym3_Law1482

theorem Equation1483_not_definableFrom_Equation895 :
    ¬ Law1483.DefinableFrom Law895 :=
  not_definableFrom_transport (sym3M895 : Magma (Fin 4)) sym3M895_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M895_endo sym3.htr
    nosym3_Law1483

theorem Equation1485_not_definableFrom_Equation895 :
    ¬ Law1485.DefinableFrom Law895 :=
  not_definableFrom_transport (sym3M895 : Magma (Fin 4)) sym3M895_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M895_endo sym3.htr
    nosym3_Law1485

theorem Equation1482_not_definableFrom_Equation978 :
    ¬ Law1482.DefinableFrom Law978 :=
  not_definableFrom_transport (sym3M978 : Magma (Fin 4)) sym3M978_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M978_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation1523 :
    ¬ Law1482.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym3M1523 : Magma (Fin 4)) sym3M1523_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M1523_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation1682 :
    ¬ Law1482.DefinableFrom Law1682 :=
  not_definableFrom_transport (sym3M1682 : Magma (Fin 4)) sym3M1682_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M1682_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation3607 :
    ¬ Law1482.DefinableFrom Law3607 :=
  not_definableFrom_transport (sym3M3607 : Magma (Fin 4)) sym3M3607_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M3607_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation3675 :
    ¬ Law1482.DefinableFrom Law3675 :=
  not_definableFrom_transport (sym3M3675 : Magma (Fin 4)) sym3M3675_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M3675_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation4364 :
    ¬ Law1482.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym3M4364 : Magma (Fin 4)) sym3M4364_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M4364_endo sym3.htr
    nosym3_Law1482

theorem Equation1482_not_definableFrom_Equation4541 :
    ¬ Law1482.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym3M4541 : Magma (Fin 4)) sym3M4541_models
    sym3.E sym3.Einv sym3.rep sym3.tr sym3.hl sym3.hr sym3M4541_endo sym3.htr
    nosym3_Law1482
