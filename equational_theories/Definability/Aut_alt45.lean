import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: A4 fixing a point of Fin 5

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 3125 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### A4 fixing a point of Fin 5 -/

namespace alt45

/-- The 12 permutations of `Fin 5`, and their inverses. -/
def E : Fin 12 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![0, 1, 3, 4, 2], ![0, 1, 4, 2, 3], ![0, 2, 1, 4, 3], ![0, 2, 3, 1, 4], ![0, 2, 4, 3, 1], ![0, 3, 1, 2, 4], ![0, 3, 2, 4, 1], ![0, 3, 4, 1, 2], ![0, 4, 1, 3, 2], ![0, 4, 2, 1, 3], ![0, 4, 3, 2, 1]]

def Einv : Fin 12 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], ![0, 2, 1, 4, 3], ![0, 3, 1, 2, 4], ![0, 4, 1, 3, 2], ![0, 2, 3, 1, 4], ![0, 4, 2, 1, 3], ![0, 3, 4, 1, 2], ![0, 2, 4, 3, 1], ![0, 3, 2, 4, 1], ![0, 4, 3, 2, 1]]

/-- One ordered pair per orbit (5 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 5 → Fin 5 × Fin 5 := ![(0, 0), (0, 1), (1, 0), (1, 1), (1, 2)]

def tr : Fin 5 → Fin 5 → Fin 5 × Fin 12 := fun x y ↦
  ![![(0, 0), (1, 0), (1, 3), (1, 6), (1, 9)], ![(2, 0), (3, 0), (4, 0), (4, 1), (4, 2)], ![(2, 3), (4, 3), (3, 3), (4, 4), (4, 5)], ![(2, 6), (4, 6), (4, 7), (3, 6), (4, 8)], ![(2, 9), (4, 9), (4, 10), (4, 11), (3, 9)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end alt45

/-! ### The refuted targets -/

/-- No alt45-invariant operation on `Fin 5` satisfies equation 464. -/
theorem noalt45_Law464 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport alt45.E alt45.tr v)).IsEndo (alt45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport alt45.E alt45.tr v)) Law464 := by
  simp only [Law464.models_iff]
  native_decide

/-- No alt45-invariant operation on `Fin 5` satisfies equation 492. -/
theorem noalt45_Law492 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport alt45.E alt45.tr v)).IsEndo (alt45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport alt45.E alt45.tr v)) Law492 := by
  simp only [Law492.models_iff]
  native_decide

/-- No alt45-invariant operation on `Fin 5` satisfies equation 543. -/
theorem noalt45_Law543 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport alt45.E alt45.tr v)).IsEndo (alt45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport alt45.E alt45.tr v)) Law543 := by
  simp only [Law543.models_iff]
  native_decide

/-- No alt45-invariant operation on `Fin 5` satisfies equation 546. -/
theorem noalt45_Law546 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport alt45.E alt45.tr v)).IsEndo (alt45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport alt45.E alt45.tr v)) Law546 := by
  simp only [Law546.models_iff]
  native_decide

/-- No alt45-invariant operation on `Fin 5` satisfies equation 895. -/
theorem noalt45_Law895 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport alt45.E alt45.tr v)).IsEndo (alt45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport alt45.E alt45.tr v)) Law895 := by
  simp only [Law895.models_iff]
  native_decide

/-- No alt45-invariant operation on `Fin 5` satisfies equation 898. -/
theorem noalt45_Law898 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport alt45.E alt45.tr v)).IsEndo (alt45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport alt45.E alt45.tr v)) Law898 := by
  simp only [Law898.models_iff]
  native_decide

/-- No alt45-invariant operation on `Fin 5` satisfies equation 1117. -/
theorem noalt45_Law1117 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport alt45.E alt45.tr v)).IsEndo (alt45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport alt45.E alt45.tr v)) Law1117 := by
  simp only [Law1117.models_iff]
  native_decide

/-! ### The sources -/

/-- A model of equation 40 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M40 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M40_models : @satisfies _ (Fin 5) alt45M40 Law40 :=
  (@Law40.models_iff (Fin 5) alt45M40).mpr (by native_decide)

theorem alt45M40_endo : ∀ i, alt45M40.IsEndo (alt45.E i) := by decide

/-- A model of equation 481 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M481 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 3, 4, 2], ![2, 4, 0, 1, 3], ![3, 2, 4, 0, 1], ![4, 3, 1, 2, 0]] x y

theorem alt45M481_models : @satisfies _ (Fin 5) alt45M481 Law481 :=
  (@Law481.models_iff (Fin 5) alt45M481).mpr (by native_decide)

theorem alt45M481_endo : ∀ i, alt45M481.IsEndo (alt45.E i) := by decide

/-- A model of equation 508 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M508 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 2, 3, 4], ![2, 1, 0, 3, 4], ![3, 1, 2, 0, 4], ![4, 1, 2, 3, 0]] x y

theorem alt45M508_models : @satisfies _ (Fin 5) alt45M508 Law508 :=
  (@Law508.models_iff (Fin 5) alt45M508).mpr (by native_decide)

theorem alt45M508_endo : ∀ i, alt45M508.IsEndo (alt45.E i) := by decide

/-- A model of equation 695 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M695 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 3, 4, 2], ![2, 4, 0, 1, 3], ![3, 2, 4, 0, 1], ![4, 3, 1, 2, 0]] x y

theorem alt45M695_models : @satisfies _ (Fin 5) alt45M695 Law695 :=
  (@Law695.models_iff (Fin 5) alt45M695).mpr (by native_decide)

theorem alt45M695_endo : ∀ i, alt45M695.IsEndo (alt45.E i) := by decide

/-- A model of equation 978 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M978 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 3, 4, 2], ![2, 4, 0, 1, 3], ![3, 2, 4, 0, 1], ![4, 3, 1, 2, 0]] x y

theorem alt45M978_models : @satisfies _ (Fin 5) alt45M978 Law978 :=
  (@Law978.models_iff (Fin 5) alt45M978).mpr (by native_decide)

theorem alt45M978_endo : ∀ i, alt45M978.IsEndo (alt45.E i) := by decide

/-- A model of equation 1523 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M1523 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 0, 0, 0], ![2, 0, 0, 0, 0], ![3, 0, 0, 0, 0], ![4, 0, 0, 0, 0]] x y

theorem alt45M1523_models : @satisfies _ (Fin 5) alt45M1523 Law1523 :=
  (@Law1523.models_iff (Fin 5) alt45M1523).mpr (by native_decide)

theorem alt45M1523_endo : ∀ i, alt45M1523.IsEndo (alt45.E i) := by decide

/-- A model of equation 1682 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M1682 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 3, 4, 2], ![2, 4, 0, 1, 3], ![3, 2, 4, 0, 1], ![4, 3, 1, 2, 0]] x y

theorem alt45M1682_models : @satisfies _ (Fin 5) alt45M1682 Law1682 :=
  (@Law1682.models_iff (Fin 5) alt45M1682).mpr (by native_decide)

theorem alt45M1682_endo : ∀ i, alt45M1682.IsEndo (alt45.E i) := by decide

/-- A model of equation 3364 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M3364 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M3364_models : @satisfies _ (Fin 5) alt45M3364 Law3364 :=
  (@Law3364.models_iff (Fin 5) alt45M3364).mpr (by native_decide)

theorem alt45M3364_endo : ∀ i, alt45M3364.IsEndo (alt45.E i) := by decide

/-- A model of equation 3607 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M3607 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M3607_models : @satisfies _ (Fin 5) alt45M3607 Law3607 :=
  (@Law3607.models_iff (Fin 5) alt45M3607).mpr (by native_decide)

theorem alt45M3607_endo : ∀ i, alt45M3607.IsEndo (alt45.E i) := by decide

/-- A model of equation 3620 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M3620 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M3620_models : @satisfies _ (Fin 5) alt45M3620 Law3620 :=
  (@Law3620.models_iff (Fin 5) alt45M3620).mpr (by native_decide)

theorem alt45M3620_endo : ∀ i, alt45M3620.IsEndo (alt45.E i) := by decide

/-- A model of equation 3675 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M3675 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M3675_models : @satisfies _ (Fin 5) alt45M3675 Law3675 :=
  (@Law3675.models_iff (Fin 5) alt45M3675).mpr (by native_decide)

theorem alt45M3675_endo : ∀ i, alt45M3675.IsEndo (alt45.E i) := by decide

/-- A model of equation 4321 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M4321 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M4321_models : @satisfies _ (Fin 5) alt45M4321 Law4321 :=
  (@Law4321.models_iff (Fin 5) alt45M4321).mpr (by native_decide)

theorem alt45M4321_endo : ∀ i, alt45M4321.IsEndo (alt45.E i) := by decide

/-- A model of equation 4364 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M4364 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M4364_models : @satisfies _ (Fin 5) alt45M4364 Law4364 :=
  (@Law4364.models_iff (Fin 5) alt45M4364).mpr (by native_decide)

theorem alt45M4364_endo : ∀ i, alt45M4364.IsEndo (alt45.E i) := by decide

/-- A model of equation 4369 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M4369 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M4369_models : @satisfies _ (Fin 5) alt45M4369 Law4369 :=
  (@Law4369.models_iff (Fin 5) alt45M4369).mpr (by native_decide)

theorem alt45M4369_endo : ∀ i, alt45M4369.IsEndo (alt45.E i) := by decide

/-- A model of equation 4415 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M4415 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M4415_models : @satisfies _ (Fin 5) alt45M4415 Law4415 :=
  (@Law4415.models_iff (Fin 5) alt45M4415).mpr (by native_decide)

theorem alt45M4415_endo : ∀ i, alt45M4415.IsEndo (alt45.E i) := by decide

/-- A model of equation 4443 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M4443 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M4443_models : @satisfies _ (Fin 5) alt45M4443 Law4443 :=
  (@Law4443.models_iff (Fin 5) alt45M4443).mpr (by native_decide)

theorem alt45M4443_endo : ∀ i, alt45M4443.IsEndo (alt45.E i) := by decide

/-- A model of equation 4541 on `Fin 5` invariant under alt45. -/
@[reducible]
def alt45M4541 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem alt45M4541_models : @satisfies _ (Fin 5) alt45M4541 Law4541 :=
  (@Law4541.models_iff (Fin 5) alt45M4541).mpr (by native_decide)

theorem alt45M4541_endo : ∀ i, alt45M4541.IsEndo (alt45.E i) := by decide

/-! ### The refutations -- 49 cells -/

theorem Equation464_not_definableFrom_Equation40 :
    ¬ Law464.DefinableFrom Law40 :=
  not_definableFrom_transport (alt45M40 : Magma (Fin 5)) alt45M40_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M40_endo alt45.htr
    noalt45_Law464

theorem Equation492_not_definableFrom_Equation40 :
    ¬ Law492.DefinableFrom Law40 :=
  not_definableFrom_transport (alt45M40 : Magma (Fin 5)) alt45M40_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M40_endo alt45.htr
    noalt45_Law492

theorem Equation543_not_definableFrom_Equation40 :
    ¬ Law543.DefinableFrom Law40 :=
  not_definableFrom_transport (alt45M40 : Magma (Fin 5)) alt45M40_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M40_endo alt45.htr
    noalt45_Law543

theorem Equation1117_not_definableFrom_Equation40 :
    ¬ Law1117.DefinableFrom Law40 :=
  not_definableFrom_transport (alt45M40 : Magma (Fin 5)) alt45M40_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M40_endo alt45.htr
    noalt45_Law1117

theorem Equation464_not_definableFrom_Equation481 :
    ¬ Law464.DefinableFrom Law481 :=
  not_definableFrom_transport (alt45M481 : Magma (Fin 5)) alt45M481_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M481_endo alt45.htr
    noalt45_Law464

theorem Equation492_not_definableFrom_Equation481 :
    ¬ Law492.DefinableFrom Law481 :=
  not_definableFrom_transport (alt45M481 : Magma (Fin 5)) alt45M481_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M481_endo alt45.htr
    noalt45_Law492

theorem Equation543_not_definableFrom_Equation481 :
    ¬ Law543.DefinableFrom Law481 :=
  not_definableFrom_transport (alt45M481 : Magma (Fin 5)) alt45M481_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M481_endo alt45.htr
    noalt45_Law543

theorem Equation546_not_definableFrom_Equation481 :
    ¬ Law546.DefinableFrom Law481 :=
  not_definableFrom_transport (alt45M481 : Magma (Fin 5)) alt45M481_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M481_endo alt45.htr
    noalt45_Law546

theorem Equation895_not_definableFrom_Equation481 :
    ¬ Law895.DefinableFrom Law481 :=
  not_definableFrom_transport (alt45M481 : Magma (Fin 5)) alt45M481_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M481_endo alt45.htr
    noalt45_Law895

theorem Equation898_not_definableFrom_Equation481 :
    ¬ Law898.DefinableFrom Law481 :=
  not_definableFrom_transport (alt45M481 : Magma (Fin 5)) alt45M481_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M481_endo alt45.htr
    noalt45_Law898

theorem Equation1117_not_definableFrom_Equation481 :
    ¬ Law1117.DefinableFrom Law481 :=
  not_definableFrom_transport (alt45M481 : Magma (Fin 5)) alt45M481_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M481_endo alt45.htr
    noalt45_Law1117

theorem Equation464_not_definableFrom_Equation508 :
    ¬ Law464.DefinableFrom Law508 :=
  not_definableFrom_transport (alt45M508 : Magma (Fin 5)) alt45M508_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M508_endo alt45.htr
    noalt45_Law464

theorem Equation492_not_definableFrom_Equation508 :
    ¬ Law492.DefinableFrom Law508 :=
  not_definableFrom_transport (alt45M508 : Magma (Fin 5)) alt45M508_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M508_endo alt45.htr
    noalt45_Law492

theorem Equation543_not_definableFrom_Equation508 :
    ¬ Law543.DefinableFrom Law508 :=
  not_definableFrom_transport (alt45M508 : Magma (Fin 5)) alt45M508_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M508_endo alt45.htr
    noalt45_Law543

theorem Equation1117_not_definableFrom_Equation508 :
    ¬ Law1117.DefinableFrom Law508 :=
  not_definableFrom_transport (alt45M508 : Magma (Fin 5)) alt45M508_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M508_endo alt45.htr
    noalt45_Law1117

theorem Equation464_not_definableFrom_Equation695 :
    ¬ Law464.DefinableFrom Law695 :=
  not_definableFrom_transport (alt45M695 : Magma (Fin 5)) alt45M695_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M695_endo alt45.htr
    noalt45_Law464

theorem Equation492_not_definableFrom_Equation695 :
    ¬ Law492.DefinableFrom Law695 :=
  not_definableFrom_transport (alt45M695 : Magma (Fin 5)) alt45M695_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M695_endo alt45.htr
    noalt45_Law492

theorem Equation543_not_definableFrom_Equation695 :
    ¬ Law543.DefinableFrom Law695 :=
  not_definableFrom_transport (alt45M695 : Magma (Fin 5)) alt45M695_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M695_endo alt45.htr
    noalt45_Law543

theorem Equation546_not_definableFrom_Equation695 :
    ¬ Law546.DefinableFrom Law695 :=
  not_definableFrom_transport (alt45M695 : Magma (Fin 5)) alt45M695_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M695_endo alt45.htr
    noalt45_Law546

theorem Equation895_not_definableFrom_Equation695 :
    ¬ Law895.DefinableFrom Law695 :=
  not_definableFrom_transport (alt45M695 : Magma (Fin 5)) alt45M695_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M695_endo alt45.htr
    noalt45_Law895

theorem Equation898_not_definableFrom_Equation695 :
    ¬ Law898.DefinableFrom Law695 :=
  not_definableFrom_transport (alt45M695 : Magma (Fin 5)) alt45M695_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M695_endo alt45.htr
    noalt45_Law898

theorem Equation1117_not_definableFrom_Equation695 :
    ¬ Law1117.DefinableFrom Law695 :=
  not_definableFrom_transport (alt45M695 : Magma (Fin 5)) alt45M695_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M695_endo alt45.htr
    noalt45_Law1117

theorem Equation464_not_definableFrom_Equation978 :
    ¬ Law464.DefinableFrom Law978 :=
  not_definableFrom_transport (alt45M978 : Magma (Fin 5)) alt45M978_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M978_endo alt45.htr
    noalt45_Law464

theorem Equation492_not_definableFrom_Equation978 :
    ¬ Law492.DefinableFrom Law978 :=
  not_definableFrom_transport (alt45M978 : Magma (Fin 5)) alt45M978_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M978_endo alt45.htr
    noalt45_Law492

theorem Equation543_not_definableFrom_Equation978 :
    ¬ Law543.DefinableFrom Law978 :=
  not_definableFrom_transport (alt45M978 : Magma (Fin 5)) alt45M978_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M978_endo alt45.htr
    noalt45_Law543

theorem Equation1117_not_definableFrom_Equation978 :
    ¬ Law1117.DefinableFrom Law978 :=
  not_definableFrom_transport (alt45M978 : Magma (Fin 5)) alt45M978_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M978_endo alt45.htr
    noalt45_Law1117

theorem Equation464_not_definableFrom_Equation1523 :
    ¬ Law464.DefinableFrom Law1523 :=
  not_definableFrom_transport (alt45M1523 : Magma (Fin 5)) alt45M1523_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M1523_endo alt45.htr
    noalt45_Law464

theorem Equation492_not_definableFrom_Equation1523 :
    ¬ Law492.DefinableFrom Law1523 :=
  not_definableFrom_transport (alt45M1523 : Magma (Fin 5)) alt45M1523_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M1523_endo alt45.htr
    noalt45_Law492

theorem Equation543_not_definableFrom_Equation1523 :
    ¬ Law543.DefinableFrom Law1523 :=
  not_definableFrom_transport (alt45M1523 : Magma (Fin 5)) alt45M1523_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M1523_endo alt45.htr
    noalt45_Law543

theorem Equation1117_not_definableFrom_Equation1523 :
    ¬ Law1117.DefinableFrom Law1523 :=
  not_definableFrom_transport (alt45M1523 : Magma (Fin 5)) alt45M1523_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M1523_endo alt45.htr
    noalt45_Law1117

theorem Equation1117_not_definableFrom_Equation1682 :
    ¬ Law1117.DefinableFrom Law1682 :=
  not_definableFrom_transport (alt45M1682 : Magma (Fin 5)) alt45M1682_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M1682_endo alt45.htr
    noalt45_Law1117

theorem Equation464_not_definableFrom_Equation3364 :
    ¬ Law464.DefinableFrom Law3364 :=
  not_definableFrom_transport (alt45M3364 : Magma (Fin 5)) alt45M3364_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M3364_endo alt45.htr
    noalt45_Law464

theorem Equation492_not_definableFrom_Equation3364 :
    ¬ Law492.DefinableFrom Law3364 :=
  not_definableFrom_transport (alt45M3364 : Magma (Fin 5)) alt45M3364_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M3364_endo alt45.htr
    noalt45_Law492

theorem Equation464_not_definableFrom_Equation3607 :
    ¬ Law464.DefinableFrom Law3607 :=
  not_definableFrom_transport (alt45M3607 : Magma (Fin 5)) alt45M3607_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M3607_endo alt45.htr
    noalt45_Law464

theorem Equation1117_not_definableFrom_Equation3607 :
    ¬ Law1117.DefinableFrom Law3607 :=
  not_definableFrom_transport (alt45M3607 : Magma (Fin 5)) alt45M3607_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M3607_endo alt45.htr
    noalt45_Law1117

theorem Equation1117_not_definableFrom_Equation3620 :
    ¬ Law1117.DefinableFrom Law3620 :=
  not_definableFrom_transport (alt45M3620 : Magma (Fin 5)) alt45M3620_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M3620_endo alt45.htr
    noalt45_Law1117

theorem Equation1117_not_definableFrom_Equation3675 :
    ¬ Law1117.DefinableFrom Law3675 :=
  not_definableFrom_transport (alt45M3675 : Magma (Fin 5)) alt45M3675_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M3675_endo alt45.htr
    noalt45_Law1117

theorem Equation464_not_definableFrom_Equation4321 :
    ¬ Law464.DefinableFrom Law4321 :=
  not_definableFrom_transport (alt45M4321 : Magma (Fin 5)) alt45M4321_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4321_endo alt45.htr
    noalt45_Law464

theorem Equation464_not_definableFrom_Equation4364 :
    ¬ Law464.DefinableFrom Law4364 :=
  not_definableFrom_transport (alt45M4364 : Magma (Fin 5)) alt45M4364_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4364_endo alt45.htr
    noalt45_Law464

theorem Equation492_not_definableFrom_Equation4364 :
    ¬ Law492.DefinableFrom Law4364 :=
  not_definableFrom_transport (alt45M4364 : Magma (Fin 5)) alt45M4364_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4364_endo alt45.htr
    noalt45_Law492

theorem Equation543_not_definableFrom_Equation4364 :
    ¬ Law543.DefinableFrom Law4364 :=
  not_definableFrom_transport (alt45M4364 : Magma (Fin 5)) alt45M4364_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4364_endo alt45.htr
    noalt45_Law543

theorem Equation1117_not_definableFrom_Equation4364 :
    ¬ Law1117.DefinableFrom Law4364 :=
  not_definableFrom_transport (alt45M4364 : Magma (Fin 5)) alt45M4364_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4364_endo alt45.htr
    noalt45_Law1117

theorem Equation1117_not_definableFrom_Equation4369 :
    ¬ Law1117.DefinableFrom Law4369 :=
  not_definableFrom_transport (alt45M4369 : Magma (Fin 5)) alt45M4369_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4369_endo alt45.htr
    noalt45_Law1117

theorem Equation464_not_definableFrom_Equation4415 :
    ¬ Law464.DefinableFrom Law4415 :=
  not_definableFrom_transport (alt45M4415 : Magma (Fin 5)) alt45M4415_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4415_endo alt45.htr
    noalt45_Law464

theorem Equation464_not_definableFrom_Equation4443 :
    ¬ Law464.DefinableFrom Law4443 :=
  not_definableFrom_transport (alt45M4443 : Magma (Fin 5)) alt45M4443_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4443_endo alt45.htr
    noalt45_Law464

theorem Equation464_not_definableFrom_Equation4541 :
    ¬ Law464.DefinableFrom Law4541 :=
  not_definableFrom_transport (alt45M4541 : Magma (Fin 5)) alt45M4541_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4541_endo alt45.htr
    noalt45_Law464

theorem Equation492_not_definableFrom_Equation4541 :
    ¬ Law492.DefinableFrom Law4541 :=
  not_definableFrom_transport (alt45M4541 : Magma (Fin 5)) alt45M4541_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4541_endo alt45.htr
    noalt45_Law492

theorem Equation543_not_definableFrom_Equation4541 :
    ¬ Law543.DefinableFrom Law4541 :=
  not_definableFrom_transport (alt45M4541 : Magma (Fin 5)) alt45M4541_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4541_endo alt45.htr
    noalt45_Law543

theorem Equation1117_not_definableFrom_Equation4541 :
    ¬ Law1117.DefinableFrom Law4541 :=
  not_definableFrom_transport (alt45M4541 : Magma (Fin 5)) alt45M4541_models
    alt45.E alt45.Einv alt45.rep alt45.tr alt45.hl alt45.hr alt45M4541_endo alt45.htr
    noalt45_Law1117
