import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: S4 fixing a point of Fin 5

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 3125 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### S4 fixing a point of Fin 5 -/

namespace sym45

/-- The 24 permutations of `Fin 5`, and their inverses. -/
def E : Fin 24 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 1, 3, 2, 4], ![0, 1, 3, 4, 2], ![0, 1, 4, 2, 3], ![0, 1, 4, 3, 2], ![0, 2, 1, 3, 4], ![0, 2, 1, 4, 3], ![0, 2, 3, 1, 4], ![0, 2, 3, 4, 1], ![0, 2, 4, 1, 3], ![0, 2, 4, 3, 1], ![0, 3, 1, 2, 4], ![0, 3, 1, 4, 2], ![0, 3, 2, 1, 4], ![0, 3, 2, 4, 1], ![0, 3, 4, 1, 2], ![0, 3, 4, 2, 1], ![0, 4, 1, 2, 3], ![0, 4, 1, 3, 2], ![0, 4, 2, 1, 3], ![0, 4, 2, 3, 1], ![0, 4, 3, 1, 2], ![0, 4, 3, 2, 1]]

def Einv : Fin 24 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 1, 3, 2, 4], ![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], ![0, 1, 4, 3, 2], ![0, 2, 1, 3, 4], ![0, 2, 1, 4, 3], ![0, 3, 1, 2, 4], ![0, 4, 1, 2, 3], ![0, 3, 1, 4, 2], ![0, 4, 1, 3, 2], ![0, 2, 3, 1, 4], ![0, 2, 4, 1, 3], ![0, 3, 2, 1, 4], ![0, 4, 2, 1, 3], ![0, 3, 4, 1, 2], ![0, 4, 3, 1, 2], ![0, 2, 3, 4, 1], ![0, 2, 4, 3, 1], ![0, 3, 2, 4, 1], ![0, 4, 2, 3, 1], ![0, 3, 4, 2, 1], ![0, 4, 3, 2, 1]]

/-- One ordered pair per orbit (5 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 5 → Fin 5 × Fin 5 := ![(0, 0), (0, 1), (1, 0), (1, 1), (1, 2)]

def tr : Fin 5 → Fin 5 → Fin 5 × Fin 24 := fun x y ↦
  ![![(0, 0), (1, 0), (1, 6), (1, 12), (1, 18)], ![(2, 0), (3, 0), (4, 0), (4, 2), (4, 4)], ![(2, 6), (4, 6), (3, 6), (4, 8), (4, 10)], ![(2, 12), (4, 12), (4, 14), (3, 12), (4, 16)], ![(2, 18), (4, 18), (4, 20), (4, 22), (3, 18)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end sym45

/-! ### The refuted targets -/

/-- No sym45-invariant operation on `Fin 5` satisfies equation 14. -/
theorem nosym45_Law14 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law14 := by
  simp only [Law14.models_iff]
  native_decide

/-- No sym45-invariant operation on `Fin 5` satisfies equation 477. -/
theorem nosym45_Law477 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law477 := by
  simp only [Law477.models_iff]
  native_decide

/-- No sym45-invariant operation on `Fin 5` satisfies equation 680. -/
theorem nosym45_Law680 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law680 := by
  simp only [Law680.models_iff]
  native_decide

/-- No sym45-invariant operation on `Fin 5` satisfies equation 692. -/
theorem nosym45_Law692 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law692 := by
  simp only [Law692.models_iff]
  native_decide

/-- No sym45-invariant operation on `Fin 5` satisfies equation 707. -/
theorem nosym45_Law707 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law707 := by
  simp only [Law707.models_iff]
  native_decide

/-- No sym45-invariant operation on `Fin 5` satisfies equation 870. -/
theorem nosym45_Law870 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law870 := by
  simp only [Law870.models_iff]
  native_decide

/-- No sym45-invariant operation on `Fin 5` satisfies equation 917. -/
theorem nosym45_Law917 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law917 := by
  simp only [Law917.models_iff]
  native_decide

/-- No sym45-invariant operation on `Fin 5` satisfies equation 978. -/
theorem nosym45_Law978 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law978 := by
  simp only [Law978.models_iff]
  native_decide

/-- No sym45-invariant operation on `Fin 5` satisfies equation 1113. -/
theorem nosym45_Law1113 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law1113 := by
  simp only [Law1113.models_iff]
  native_decide

/-- No sym45-invariant operation on `Fin 5` satisfies equation 1276. -/
theorem nosym45_Law1276 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport sym45.E sym45.tr v)).IsEndo (sym45.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport sym45.E sym45.tr v)) Law1276 := by
  simp only [Law1276.models_iff]
  native_decide

/-! ### The sources -/

/-- A model of equation 40 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M40 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M40_models : @satisfies _ (Fin 5) sym45M40 Law40 :=
  (@Law40.models_iff (Fin 5) sym45M40).mpr (by native_decide)

theorem sym45M40_endo : ∀ i, sym45M40.IsEndo (sym45.E i) := by decide

/-- A model of equation 43 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M43 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M43_models : @satisfies _ (Fin 5) sym45M43 Law43 :=
  (@Law43.models_iff (Fin 5) sym45M43).mpr (by native_decide)

theorem sym45M43_endo : ∀ i, sym45M43.IsEndo (sym45.E i) := by decide

/-- A model of equation 313 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M313 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M313_models : @satisfies _ (Fin 5) sym45M313 Law313 :=
  (@Law313.models_iff (Fin 5) sym45M313).mpr (by native_decide)

theorem sym45M313_endo : ∀ i, sym45M313.IsEndo (sym45.E i) := by decide

/-- A model of equation 332 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M332 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M332_models : @satisfies _ (Fin 5) sym45M332 Law332 :=
  (@Law332.models_iff (Fin 5) sym45M332).mpr (by native_decide)

theorem sym45M332_endo : ∀ i, sym45M332.IsEndo (sym45.E i) := by decide

/-- A model of equation 335 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M335 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M335_models : @satisfies _ (Fin 5) sym45M335 Law335 :=
  (@Law335.models_iff (Fin 5) sym45M335).mpr (by native_decide)

theorem sym45M335_endo : ∀ i, sym45M335.IsEndo (sym45.E i) := by decide

/-- A model of equation 504 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M504 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 2, 3, 4], ![2, 1, 0, 3, 4], ![3, 1, 2, 0, 4], ![4, 1, 2, 3, 0]] x y

theorem sym45M504_models : @satisfies _ (Fin 5) sym45M504 Law504 :=
  (@Law504.models_iff (Fin 5) sym45M504).mpr (by native_decide)

theorem sym45M504_endo : ∀ i, sym45M504.IsEndo (sym45.E i) := by decide

/-- A model of equation 508 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M508 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 2, 3, 4], ![2, 1, 0, 3, 4], ![3, 1, 2, 0, 4], ![4, 1, 2, 3, 0]] x y

theorem sym45M508_models : @satisfies _ (Fin 5) sym45M508 Law508 :=
  (@Law508.models_iff (Fin 5) sym45M508).mpr (by native_decide)

theorem sym45M508_endo : ∀ i, sym45M508.IsEndo (sym45.E i) := by decide

/-- A model of equation 1519 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M1519 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 0, 0, 0], ![2, 0, 0, 0, 0], ![3, 0, 0, 0, 0], ![4, 0, 0, 0, 0]] x y

theorem sym45M1519_models : @satisfies _ (Fin 5) sym45M1519 Law1519 :=
  (@Law1519.models_iff (Fin 5) sym45M1519).mpr (by native_decide)

theorem sym45M1519_endo : ∀ i, sym45M1519.IsEndo (sym45.E i) := by decide

/-- A model of equation 1523 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M1523 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 1, 2, 3, 4], ![1, 0, 0, 0, 0], ![2, 0, 0, 0, 0], ![3, 0, 0, 0, 0], ![4, 0, 0, 0, 0]] x y

theorem sym45M1523_models : @satisfies _ (Fin 5) sym45M1523 Law1523 :=
  (@Law1523.models_iff (Fin 5) sym45M1523).mpr (by native_decide)

theorem sym45M1523_endo : ∀ i, sym45M1523.IsEndo (sym45.E i) := by decide

/-- A model of equation 3269 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3269 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3269_models : @satisfies _ (Fin 5) sym45M3269 Law3269 :=
  (@Law3269.models_iff (Fin 5) sym45M3269).mpr (by native_decide)

theorem sym45M3269_endo : ∀ i, sym45M3269.IsEndo (sym45.E i) := by decide

/-- A model of equation 3272 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3272 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3272_models : @satisfies _ (Fin 5) sym45M3272 Law3272 :=
  (@Law3272.models_iff (Fin 5) sym45M3272).mpr (by native_decide)

theorem sym45M3272_endo : ∀ i, sym45M3272.IsEndo (sym45.E i) := by decide

/-- A model of equation 3279 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3279 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3279_models : @satisfies _ (Fin 5) sym45M3279 Law3279 :=
  (@Law3279.models_iff (Fin 5) sym45M3279).mpr (by native_decide)

theorem sym45M3279_endo : ∀ i, sym45M3279.IsEndo (sym45.E i) := by decide

/-- A model of equation 3342 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3342 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3342_models : @satisfies _ (Fin 5) sym45M3342 Law3342 :=
  (@Law3342.models_iff (Fin 5) sym45M3342).mpr (by native_decide)

theorem sym45M3342_endo : ∀ i, sym45M3342.IsEndo (sym45.E i) := by decide

/-- A model of equation 3352 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3352 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3352_models : @satisfies _ (Fin 5) sym45M3352 Law3352 :=
  (@Law3352.models_iff (Fin 5) sym45M3352).mpr (by native_decide)

theorem sym45M3352_endo : ∀ i, sym45M3352.IsEndo (sym45.E i) := by decide

/-- A model of equation 3364 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3364 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3364_models : @satisfies _ (Fin 5) sym45M3364 Law3364 :=
  (@Law3364.models_iff (Fin 5) sym45M3364).mpr (by native_decide)

theorem sym45M3364_endo : ∀ i, sym45M3364.IsEndo (sym45.E i) := by decide

/-- A model of equation 3472 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3472 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3472_models : @satisfies _ (Fin 5) sym45M3472 Law3472 :=
  (@Law3472.models_iff (Fin 5) sym45M3472).mpr (by native_decide)

theorem sym45M3472_endo : ∀ i, sym45M3472.IsEndo (sym45.E i) := by decide

/-- A model of equation 3475 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3475 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3475_models : @satisfies _ (Fin 5) sym45M3475 Law3475 :=
  (@Law3475.models_iff (Fin 5) sym45M3475).mpr (by native_decide)

theorem sym45M3475_endo : ∀ i, sym45M3475.IsEndo (sym45.E i) := by decide

/-- A model of equation 3482 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3482 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3482_models : @satisfies _ (Fin 5) sym45M3482 Law3482 :=
  (@Law3482.models_iff (Fin 5) sym45M3482).mpr (by native_decide)

theorem sym45M3482_endo : ∀ i, sym45M3482.IsEndo (sym45.E i) := by decide

/-- A model of equation 3545 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3545 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3545_models : @satisfies _ (Fin 5) sym45M3545 Law3545 :=
  (@Law3545.models_iff (Fin 5) sym45M3545).mpr (by native_decide)

theorem sym45M3545_endo : ∀ i, sym45M3545.IsEndo (sym45.E i) := by decide

/-- A model of equation 3558 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3558 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3558_models : @satisfies _ (Fin 5) sym45M3558 Law3558 :=
  (@Law3558.models_iff (Fin 5) sym45M3558).mpr (by native_decide)

theorem sym45M3558_endo : ∀ i, sym45M3558.IsEndo (sym45.E i) := by decide

/-- A model of equation 3588 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3588 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3588_models : @satisfies _ (Fin 5) sym45M3588 Law3588 :=
  (@Law3588.models_iff (Fin 5) sym45M3588).mpr (by native_decide)

theorem sym45M3588_endo : ∀ i, sym45M3588.IsEndo (sym45.E i) := by decide

/-- A model of equation 3607 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3607 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3607_models : @satisfies _ (Fin 5) sym45M3607 Law3607 :=
  (@Law3607.models_iff (Fin 5) sym45M3607).mpr (by native_decide)

theorem sym45M3607_endo : ∀ i, sym45M3607.IsEndo (sym45.E i) := by decide

/-- A model of equation 3620 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3620 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3620_models : @satisfies _ (Fin 5) sym45M3620 Law3620 :=
  (@Law3620.models_iff (Fin 5) sym45M3620).mpr (by native_decide)

theorem sym45M3620_endo : ∀ i, sym45M3620.IsEndo (sym45.E i) := by decide

/-- A model of equation 3675 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3675 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3675_models : @satisfies _ (Fin 5) sym45M3675 Law3675 :=
  (@Law3675.models_iff (Fin 5) sym45M3675).mpr (by native_decide)

theorem sym45M3675_endo : ∀ i, sym45M3675.IsEndo (sym45.E i) := by decide

/-- A model of equation 3748 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M3748 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M3748_models : @satisfies _ (Fin 5) sym45M3748 Law3748 :=
  (@Law3748.models_iff (Fin 5) sym45M3748).mpr (by native_decide)

theorem sym45M3748_endo : ∀ i, sym45M3748.IsEndo (sym45.E i) := by decide

/-- A model of equation 4273 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4273 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4273_models : @satisfies _ (Fin 5) sym45M4273 Law4273 :=
  (@Law4273.models_iff (Fin 5) sym45M4273).mpr (by native_decide)

theorem sym45M4273_endo : ∀ i, sym45M4273.IsEndo (sym45.E i) := by decide

/-- A model of equation 4293 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4293 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4293_models : @satisfies _ (Fin 5) sym45M4293 Law4293 :=
  (@Law4293.models_iff (Fin 5) sym45M4293).mpr (by native_decide)

theorem sym45M4293_endo : ∀ i, sym45M4293.IsEndo (sym45.E i) := by decide

/-- A model of equation 4321 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4321 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4321_models : @satisfies _ (Fin 5) sym45M4321 Law4321 :=
  (@Law4321.models_iff (Fin 5) sym45M4321).mpr (by native_decide)

theorem sym45M4321_endo : ∀ i, sym45M4321.IsEndo (sym45.E i) := by decide

/-- A model of equation 4343 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4343 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4343_models : @satisfies _ (Fin 5) sym45M4343 Law4343 :=
  (@Law4343.models_iff (Fin 5) sym45M4343).mpr (by native_decide)

theorem sym45M4343_endo : ∀ i, sym45M4343.IsEndo (sym45.E i) := by decide

/-- A model of equation 4364 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4364 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4364_models : @satisfies _ (Fin 5) sym45M4364 Law4364 :=
  (@Law4364.models_iff (Fin 5) sym45M4364).mpr (by native_decide)

theorem sym45M4364_endo : ∀ i, sym45M4364.IsEndo (sym45.E i) := by decide

/-- A model of equation 4369 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4369 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4369_models : @satisfies _ (Fin 5) sym45M4369 Law4369 :=
  (@Law4369.models_iff (Fin 5) sym45M4369).mpr (by native_decide)

theorem sym45M4369_endo : ∀ i, sym45M4369.IsEndo (sym45.E i) := by decide

/-- A model of equation 4405 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4405 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4405_models : @satisfies _ (Fin 5) sym45M4405 Law4405 :=
  (@Law4405.models_iff (Fin 5) sym45M4405).mpr (by native_decide)

theorem sym45M4405_endo : ∀ i, sym45M4405.IsEndo (sym45.E i) := by decide

/-- A model of equation 4415 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4415 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4415_models : @satisfies _ (Fin 5) sym45M4415 Law4415 :=
  (@Law4415.models_iff (Fin 5) sym45M4415).mpr (by native_decide)

theorem sym45M4415_endo : ∀ i, sym45M4415.IsEndo (sym45.E i) := by decide

/-- A model of equation 4443 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4443 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4443_models : @satisfies _ (Fin 5) sym45M4443 Law4443 :=
  (@Law4443.models_iff (Fin 5) sym45M4443).mpr (by native_decide)

theorem sym45M4443_endo : ∀ i, sym45M4443.IsEndo (sym45.E i) := by decide

/-- A model of equation 4541 on `Fin 5` invariant under sym45. -/
@[reducible]
def sym45M4541 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]] x y

theorem sym45M4541_models : @satisfies _ (Fin 5) sym45M4541 Law4541 :=
  (@Law4541.models_iff (Fin 5) sym45M4541).mpr (by native_decide)

theorem sym45M4541_endo : ∀ i, sym45M4541.IsEndo (sym45.E i) := by decide

/-! ### The refutations -- 152 cells -/

theorem Equation14_not_definableFrom_Equation40 :
    ¬ Law14.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation40 :
    ¬ Law477.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation40 :
    ¬ Law680.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation40 :
    ¬ Law692.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation40 :
    ¬ Law707.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law707

theorem Equation870_not_definableFrom_Equation40 :
    ¬ Law870.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation40 :
    ¬ Law917.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law917

theorem Equation978_not_definableFrom_Equation40 :
    ¬ Law978.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law978

theorem Equation1113_not_definableFrom_Equation40 :
    ¬ Law1113.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation40 :
    ¬ Law1276.DefinableFrom Law40 :=
  not_definableFrom_transport (sym45M40 : Magma (Fin 5)) sym45M40_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M40_endo sym45.htr
    nosym45_Law1276

theorem Equation707_not_definableFrom_Equation43 :
    ¬ Law707.DefinableFrom Law43 :=
  not_definableFrom_transport (sym45M43 : Magma (Fin 5)) sym45M43_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M43_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation43 :
    ¬ Law1113.DefinableFrom Law43 :=
  not_definableFrom_transport (sym45M43 : Magma (Fin 5)) sym45M43_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M43_endo sym45.htr
    nosym45_Law1113

theorem Equation14_not_definableFrom_Equation313 :
    ¬ Law14.DefinableFrom Law313 :=
  not_definableFrom_transport (sym45M313 : Magma (Fin 5)) sym45M313_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M313_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation313 :
    ¬ Law477.DefinableFrom Law313 :=
  not_definableFrom_transport (sym45M313 : Magma (Fin 5)) sym45M313_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M313_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation313 :
    ¬ Law680.DefinableFrom Law313 :=
  not_definableFrom_transport (sym45M313 : Magma (Fin 5)) sym45M313_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M313_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation313 :
    ¬ Law692.DefinableFrom Law313 :=
  not_definableFrom_transport (sym45M313 : Magma (Fin 5)) sym45M313_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M313_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation313 :
    ¬ Law707.DefinableFrom Law313 :=
  not_definableFrom_transport (sym45M313 : Magma (Fin 5)) sym45M313_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M313_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation313 :
    ¬ Law1113.DefinableFrom Law313 :=
  not_definableFrom_transport (sym45M313 : Magma (Fin 5)) sym45M313_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M313_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation313 :
    ¬ Law1276.DefinableFrom Law313 :=
  not_definableFrom_transport (sym45M313 : Magma (Fin 5)) sym45M313_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M313_endo sym45.htr
    nosym45_Law1276

theorem Equation707_not_definableFrom_Equation332 :
    ¬ Law707.DefinableFrom Law332 :=
  not_definableFrom_transport (sym45M332 : Magma (Fin 5)) sym45M332_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M332_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation332 :
    ¬ Law1113.DefinableFrom Law332 :=
  not_definableFrom_transport (sym45M332 : Magma (Fin 5)) sym45M332_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M332_endo sym45.htr
    nosym45_Law1113

theorem Equation707_not_definableFrom_Equation335 :
    ¬ Law707.DefinableFrom Law335 :=
  not_definableFrom_transport (sym45M335 : Magma (Fin 5)) sym45M335_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M335_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation335 :
    ¬ Law1113.DefinableFrom Law335 :=
  not_definableFrom_transport (sym45M335 : Magma (Fin 5)) sym45M335_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M335_endo sym45.htr
    nosym45_Law1113

theorem Equation870_not_definableFrom_Equation504 :
    ¬ Law870.DefinableFrom Law504 :=
  not_definableFrom_transport (sym45M504 : Magma (Fin 5)) sym45M504_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M504_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation504 :
    ¬ Law917.DefinableFrom Law504 :=
  not_definableFrom_transport (sym45M504 : Magma (Fin 5)) sym45M504_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M504_endo sym45.htr
    nosym45_Law917

theorem Equation14_not_definableFrom_Equation508 :
    ¬ Law14.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation508 :
    ¬ Law477.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation508 :
    ¬ Law680.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation508 :
    ¬ Law692.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation508 :
    ¬ Law707.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law707

theorem Equation870_not_definableFrom_Equation508 :
    ¬ Law870.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation508 :
    ¬ Law917.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law917

theorem Equation978_not_definableFrom_Equation508 :
    ¬ Law978.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law978

theorem Equation1113_not_definableFrom_Equation508 :
    ¬ Law1113.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation508 :
    ¬ Law1276.DefinableFrom Law508 :=
  not_definableFrom_transport (sym45M508 : Magma (Fin 5)) sym45M508_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M508_endo sym45.htr
    nosym45_Law1276

theorem Equation14_not_definableFrom_Equation1519 :
    ¬ Law14.DefinableFrom Law1519 :=
  not_definableFrom_transport (sym45M1519 : Magma (Fin 5)) sym45M1519_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1519_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation1519 :
    ¬ Law477.DefinableFrom Law1519 :=
  not_definableFrom_transport (sym45M1519 : Magma (Fin 5)) sym45M1519_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1519_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation1519 :
    ¬ Law680.DefinableFrom Law1519 :=
  not_definableFrom_transport (sym45M1519 : Magma (Fin 5)) sym45M1519_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1519_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation1519 :
    ¬ Law692.DefinableFrom Law1519 :=
  not_definableFrom_transport (sym45M1519 : Magma (Fin 5)) sym45M1519_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1519_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation1519 :
    ¬ Law707.DefinableFrom Law1519 :=
  not_definableFrom_transport (sym45M1519 : Magma (Fin 5)) sym45M1519_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1519_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation1519 :
    ¬ Law1113.DefinableFrom Law1519 :=
  not_definableFrom_transport (sym45M1519 : Magma (Fin 5)) sym45M1519_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1519_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation1519 :
    ¬ Law1276.DefinableFrom Law1519 :=
  not_definableFrom_transport (sym45M1519 : Magma (Fin 5)) sym45M1519_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1519_endo sym45.htr
    nosym45_Law1276

theorem Equation14_not_definableFrom_Equation1523 :
    ¬ Law14.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation1523 :
    ¬ Law477.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation1523 :
    ¬ Law680.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation1523 :
    ¬ Law692.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation1523 :
    ¬ Law707.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law707

theorem Equation870_not_definableFrom_Equation1523 :
    ¬ Law870.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation1523 :
    ¬ Law917.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law917

theorem Equation978_not_definableFrom_Equation1523 :
    ¬ Law978.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law978

theorem Equation1113_not_definableFrom_Equation1523 :
    ¬ Law1113.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation1523 :
    ¬ Law1276.DefinableFrom Law1523 :=
  not_definableFrom_transport (sym45M1523 : Magma (Fin 5)) sym45M1523_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M1523_endo sym45.htr
    nosym45_Law1276

theorem Equation870_not_definableFrom_Equation3269 :
    ¬ Law870.DefinableFrom Law3269 :=
  not_definableFrom_transport (sym45M3269 : Magma (Fin 5)) sym45M3269_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3269_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation3269 :
    ¬ Law917.DefinableFrom Law3269 :=
  not_definableFrom_transport (sym45M3269 : Magma (Fin 5)) sym45M3269_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3269_endo sym45.htr
    nosym45_Law917

theorem Equation14_not_definableFrom_Equation3272 :
    ¬ Law14.DefinableFrom Law3272 :=
  not_definableFrom_transport (sym45M3272 : Magma (Fin 5)) sym45M3272_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3272_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation3272 :
    ¬ Law477.DefinableFrom Law3272 :=
  not_definableFrom_transport (sym45M3272 : Magma (Fin 5)) sym45M3272_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3272_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation3272 :
    ¬ Law680.DefinableFrom Law3272 :=
  not_definableFrom_transport (sym45M3272 : Magma (Fin 5)) sym45M3272_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3272_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation3272 :
    ¬ Law692.DefinableFrom Law3272 :=
  not_definableFrom_transport (sym45M3272 : Magma (Fin 5)) sym45M3272_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3272_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation3272 :
    ¬ Law707.DefinableFrom Law3272 :=
  not_definableFrom_transport (sym45M3272 : Magma (Fin 5)) sym45M3272_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3272_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3272 :
    ¬ Law1113.DefinableFrom Law3272 :=
  not_definableFrom_transport (sym45M3272 : Magma (Fin 5)) sym45M3272_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3272_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation3272 :
    ¬ Law1276.DefinableFrom Law3272 :=
  not_definableFrom_transport (sym45M3272 : Magma (Fin 5)) sym45M3272_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3272_endo sym45.htr
    nosym45_Law1276

theorem Equation870_not_definableFrom_Equation3279 :
    ¬ Law870.DefinableFrom Law3279 :=
  not_definableFrom_transport (sym45M3279 : Magma (Fin 5)) sym45M3279_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3279_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation3279 :
    ¬ Law917.DefinableFrom Law3279 :=
  not_definableFrom_transport (sym45M3279 : Magma (Fin 5)) sym45M3279_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3279_endo sym45.htr
    nosym45_Law917

theorem Equation707_not_definableFrom_Equation3342 :
    ¬ Law707.DefinableFrom Law3342 :=
  not_definableFrom_transport (sym45M3342 : Magma (Fin 5)) sym45M3342_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3342_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3342 :
    ¬ Law1113.DefinableFrom Law3342 :=
  not_definableFrom_transport (sym45M3342 : Magma (Fin 5)) sym45M3342_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3342_endo sym45.htr
    nosym45_Law1113

theorem Equation707_not_definableFrom_Equation3352 :
    ¬ Law707.DefinableFrom Law3352 :=
  not_definableFrom_transport (sym45M3352 : Magma (Fin 5)) sym45M3352_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3352_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3352 :
    ¬ Law1113.DefinableFrom Law3352 :=
  not_definableFrom_transport (sym45M3352 : Magma (Fin 5)) sym45M3352_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3352_endo sym45.htr
    nosym45_Law1113

theorem Equation14_not_definableFrom_Equation3364 :
    ¬ Law14.DefinableFrom Law3364 :=
  not_definableFrom_transport (sym45M3364 : Magma (Fin 5)) sym45M3364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3364_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation3364 :
    ¬ Law477.DefinableFrom Law3364 :=
  not_definableFrom_transport (sym45M3364 : Magma (Fin 5)) sym45M3364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3364_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation3364 :
    ¬ Law680.DefinableFrom Law3364 :=
  not_definableFrom_transport (sym45M3364 : Magma (Fin 5)) sym45M3364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3364_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation3364 :
    ¬ Law692.DefinableFrom Law3364 :=
  not_definableFrom_transport (sym45M3364 : Magma (Fin 5)) sym45M3364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3364_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation3364 :
    ¬ Law707.DefinableFrom Law3364 :=
  not_definableFrom_transport (sym45M3364 : Magma (Fin 5)) sym45M3364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3364_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3364 :
    ¬ Law1113.DefinableFrom Law3364 :=
  not_definableFrom_transport (sym45M3364 : Magma (Fin 5)) sym45M3364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3364_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation3364 :
    ¬ Law1276.DefinableFrom Law3364 :=
  not_definableFrom_transport (sym45M3364 : Magma (Fin 5)) sym45M3364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3364_endo sym45.htr
    nosym45_Law1276

theorem Equation14_not_definableFrom_Equation3472 :
    ¬ Law14.DefinableFrom Law3472 :=
  not_definableFrom_transport (sym45M3472 : Magma (Fin 5)) sym45M3472_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3472_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation3472 :
    ¬ Law477.DefinableFrom Law3472 :=
  not_definableFrom_transport (sym45M3472 : Magma (Fin 5)) sym45M3472_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3472_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation3472 :
    ¬ Law680.DefinableFrom Law3472 :=
  not_definableFrom_transport (sym45M3472 : Magma (Fin 5)) sym45M3472_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3472_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation3472 :
    ¬ Law692.DefinableFrom Law3472 :=
  not_definableFrom_transport (sym45M3472 : Magma (Fin 5)) sym45M3472_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3472_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation3472 :
    ¬ Law707.DefinableFrom Law3472 :=
  not_definableFrom_transport (sym45M3472 : Magma (Fin 5)) sym45M3472_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3472_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3472 :
    ¬ Law1113.DefinableFrom Law3472 :=
  not_definableFrom_transport (sym45M3472 : Magma (Fin 5)) sym45M3472_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3472_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation3472 :
    ¬ Law1276.DefinableFrom Law3472 :=
  not_definableFrom_transport (sym45M3472 : Magma (Fin 5)) sym45M3472_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3472_endo sym45.htr
    nosym45_Law1276

theorem Equation870_not_definableFrom_Equation3475 :
    ¬ Law870.DefinableFrom Law3475 :=
  not_definableFrom_transport (sym45M3475 : Magma (Fin 5)) sym45M3475_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3475_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation3475 :
    ¬ Law917.DefinableFrom Law3475 :=
  not_definableFrom_transport (sym45M3475 : Magma (Fin 5)) sym45M3475_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3475_endo sym45.htr
    nosym45_Law917

theorem Equation870_not_definableFrom_Equation3482 :
    ¬ Law870.DefinableFrom Law3482 :=
  not_definableFrom_transport (sym45M3482 : Magma (Fin 5)) sym45M3482_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3482_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation3482 :
    ¬ Law917.DefinableFrom Law3482 :=
  not_definableFrom_transport (sym45M3482 : Magma (Fin 5)) sym45M3482_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3482_endo sym45.htr
    nosym45_Law917

theorem Equation707_not_definableFrom_Equation3545 :
    ¬ Law707.DefinableFrom Law3545 :=
  not_definableFrom_transport (sym45M3545 : Magma (Fin 5)) sym45M3545_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3545_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3545 :
    ¬ Law1113.DefinableFrom Law3545 :=
  not_definableFrom_transport (sym45M3545 : Magma (Fin 5)) sym45M3545_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3545_endo sym45.htr
    nosym45_Law1113

theorem Equation707_not_definableFrom_Equation3558 :
    ¬ Law707.DefinableFrom Law3558 :=
  not_definableFrom_transport (sym45M3558 : Magma (Fin 5)) sym45M3558_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3558_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3558 :
    ¬ Law1113.DefinableFrom Law3558 :=
  not_definableFrom_transport (sym45M3558 : Magma (Fin 5)) sym45M3558_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3558_endo sym45.htr
    nosym45_Law1113

theorem Equation14_not_definableFrom_Equation3588 :
    ¬ Law14.DefinableFrom Law3588 :=
  not_definableFrom_transport (sym45M3588 : Magma (Fin 5)) sym45M3588_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3588_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation3588 :
    ¬ Law477.DefinableFrom Law3588 :=
  not_definableFrom_transport (sym45M3588 : Magma (Fin 5)) sym45M3588_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3588_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation3588 :
    ¬ Law680.DefinableFrom Law3588 :=
  not_definableFrom_transport (sym45M3588 : Magma (Fin 5)) sym45M3588_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3588_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation3588 :
    ¬ Law692.DefinableFrom Law3588 :=
  not_definableFrom_transport (sym45M3588 : Magma (Fin 5)) sym45M3588_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3588_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation3588 :
    ¬ Law707.DefinableFrom Law3588 :=
  not_definableFrom_transport (sym45M3588 : Magma (Fin 5)) sym45M3588_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3588_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3588 :
    ¬ Law1113.DefinableFrom Law3588 :=
  not_definableFrom_transport (sym45M3588 : Magma (Fin 5)) sym45M3588_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3588_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation3588 :
    ¬ Law1276.DefinableFrom Law3588 :=
  not_definableFrom_transport (sym45M3588 : Magma (Fin 5)) sym45M3588_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3588_endo sym45.htr
    nosym45_Law1276

theorem Equation707_not_definableFrom_Equation3607 :
    ¬ Law707.DefinableFrom Law3607 :=
  not_definableFrom_transport (sym45M3607 : Magma (Fin 5)) sym45M3607_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3607_endo sym45.htr
    nosym45_Law707

theorem Equation870_not_definableFrom_Equation3607 :
    ¬ Law870.DefinableFrom Law3607 :=
  not_definableFrom_transport (sym45M3607 : Magma (Fin 5)) sym45M3607_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3607_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation3607 :
    ¬ Law917.DefinableFrom Law3607 :=
  not_definableFrom_transport (sym45M3607 : Magma (Fin 5)) sym45M3607_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3607_endo sym45.htr
    nosym45_Law917

theorem Equation1113_not_definableFrom_Equation3607 :
    ¬ Law1113.DefinableFrom Law3607 :=
  not_definableFrom_transport (sym45M3607 : Magma (Fin 5)) sym45M3607_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3607_endo sym45.htr
    nosym45_Law1113

theorem Equation14_not_definableFrom_Equation3620 :
    ¬ Law14.DefinableFrom Law3620 :=
  not_definableFrom_transport (sym45M3620 : Magma (Fin 5)) sym45M3620_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3620_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation3620 :
    ¬ Law477.DefinableFrom Law3620 :=
  not_definableFrom_transport (sym45M3620 : Magma (Fin 5)) sym45M3620_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3620_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation3620 :
    ¬ Law680.DefinableFrom Law3620 :=
  not_definableFrom_transport (sym45M3620 : Magma (Fin 5)) sym45M3620_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3620_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation3620 :
    ¬ Law692.DefinableFrom Law3620 :=
  not_definableFrom_transport (sym45M3620 : Magma (Fin 5)) sym45M3620_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3620_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation3620 :
    ¬ Law707.DefinableFrom Law3620 :=
  not_definableFrom_transport (sym45M3620 : Magma (Fin 5)) sym45M3620_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3620_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3620 :
    ¬ Law1113.DefinableFrom Law3620 :=
  not_definableFrom_transport (sym45M3620 : Magma (Fin 5)) sym45M3620_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3620_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation3620 :
    ¬ Law1276.DefinableFrom Law3620 :=
  not_definableFrom_transport (sym45M3620 : Magma (Fin 5)) sym45M3620_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3620_endo sym45.htr
    nosym45_Law1276

theorem Equation707_not_definableFrom_Equation3675 :
    ¬ Law707.DefinableFrom Law3675 :=
  not_definableFrom_transport (sym45M3675 : Magma (Fin 5)) sym45M3675_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3675_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3675 :
    ¬ Law1113.DefinableFrom Law3675 :=
  not_definableFrom_transport (sym45M3675 : Magma (Fin 5)) sym45M3675_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3675_endo sym45.htr
    nosym45_Law1113

theorem Equation707_not_definableFrom_Equation3748 :
    ¬ Law707.DefinableFrom Law3748 :=
  not_definableFrom_transport (sym45M3748 : Magma (Fin 5)) sym45M3748_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3748_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation3748 :
    ¬ Law1113.DefinableFrom Law3748 :=
  not_definableFrom_transport (sym45M3748 : Magma (Fin 5)) sym45M3748_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M3748_endo sym45.htr
    nosym45_Law1113

theorem Equation14_not_definableFrom_Equation4273 :
    ¬ Law14.DefinableFrom Law4273 :=
  not_definableFrom_transport (sym45M4273 : Magma (Fin 5)) sym45M4273_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4273_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation4273 :
    ¬ Law477.DefinableFrom Law4273 :=
  not_definableFrom_transport (sym45M4273 : Magma (Fin 5)) sym45M4273_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4273_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation4273 :
    ¬ Law680.DefinableFrom Law4273 :=
  not_definableFrom_transport (sym45M4273 : Magma (Fin 5)) sym45M4273_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4273_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation4273 :
    ¬ Law692.DefinableFrom Law4273 :=
  not_definableFrom_transport (sym45M4273 : Magma (Fin 5)) sym45M4273_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4273_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation4273 :
    ¬ Law707.DefinableFrom Law4273 :=
  not_definableFrom_transport (sym45M4273 : Magma (Fin 5)) sym45M4273_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4273_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation4273 :
    ¬ Law1113.DefinableFrom Law4273 :=
  not_definableFrom_transport (sym45M4273 : Magma (Fin 5)) sym45M4273_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4273_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation4273 :
    ¬ Law1276.DefinableFrom Law4273 :=
  not_definableFrom_transport (sym45M4273 : Magma (Fin 5)) sym45M4273_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4273_endo sym45.htr
    nosym45_Law1276

theorem Equation707_not_definableFrom_Equation4293 :
    ¬ Law707.DefinableFrom Law4293 :=
  not_definableFrom_transport (sym45M4293 : Magma (Fin 5)) sym45M4293_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4293_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation4293 :
    ¬ Law1113.DefinableFrom Law4293 :=
  not_definableFrom_transport (sym45M4293 : Magma (Fin 5)) sym45M4293_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4293_endo sym45.htr
    nosym45_Law1113

theorem Equation707_not_definableFrom_Equation4321 :
    ¬ Law707.DefinableFrom Law4321 :=
  not_definableFrom_transport (sym45M4321 : Magma (Fin 5)) sym45M4321_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4321_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation4321 :
    ¬ Law1113.DefinableFrom Law4321 :=
  not_definableFrom_transport (sym45M4321 : Magma (Fin 5)) sym45M4321_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4321_endo sym45.htr
    nosym45_Law1113

theorem Equation707_not_definableFrom_Equation4343 :
    ¬ Law707.DefinableFrom Law4343 :=
  not_definableFrom_transport (sym45M4343 : Magma (Fin 5)) sym45M4343_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4343_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation4343 :
    ¬ Law1113.DefinableFrom Law4343 :=
  not_definableFrom_transport (sym45M4343 : Magma (Fin 5)) sym45M4343_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4343_endo sym45.htr
    nosym45_Law1113

theorem Equation14_not_definableFrom_Equation4364 :
    ¬ Law14.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation4364 :
    ¬ Law477.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation4364 :
    ¬ Law680.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation4364 :
    ¬ Law692.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation4364 :
    ¬ Law707.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law707

theorem Equation870_not_definableFrom_Equation4364 :
    ¬ Law870.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation4364 :
    ¬ Law917.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law917

theorem Equation978_not_definableFrom_Equation4364 :
    ¬ Law978.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law978

theorem Equation1113_not_definableFrom_Equation4364 :
    ¬ Law1113.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation4364 :
    ¬ Law1276.DefinableFrom Law4364 :=
  not_definableFrom_transport (sym45M4364 : Magma (Fin 5)) sym45M4364_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4364_endo sym45.htr
    nosym45_Law1276

theorem Equation707_not_definableFrom_Equation4369 :
    ¬ Law707.DefinableFrom Law4369 :=
  not_definableFrom_transport (sym45M4369 : Magma (Fin 5)) sym45M4369_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4369_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation4369 :
    ¬ Law1113.DefinableFrom Law4369 :=
  not_definableFrom_transport (sym45M4369 : Magma (Fin 5)) sym45M4369_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4369_endo sym45.htr
    nosym45_Law1113

theorem Equation707_not_definableFrom_Equation4405 :
    ¬ Law707.DefinableFrom Law4405 :=
  not_definableFrom_transport (sym45M4405 : Magma (Fin 5)) sym45M4405_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4405_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation4405 :
    ¬ Law1113.DefinableFrom Law4405 :=
  not_definableFrom_transport (sym45M4405 : Magma (Fin 5)) sym45M4405_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4405_endo sym45.htr
    nosym45_Law1113

theorem Equation707_not_definableFrom_Equation4415 :
    ¬ Law707.DefinableFrom Law4415 :=
  not_definableFrom_transport (sym45M4415 : Magma (Fin 5)) sym45M4415_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4415_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation4415 :
    ¬ Law1113.DefinableFrom Law4415 :=
  not_definableFrom_transport (sym45M4415 : Magma (Fin 5)) sym45M4415_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4415_endo sym45.htr
    nosym45_Law1113

theorem Equation707_not_definableFrom_Equation4443 :
    ¬ Law707.DefinableFrom Law4443 :=
  not_definableFrom_transport (sym45M4443 : Magma (Fin 5)) sym45M4443_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4443_endo sym45.htr
    nosym45_Law707

theorem Equation1113_not_definableFrom_Equation4443 :
    ¬ Law1113.DefinableFrom Law4443 :=
  not_definableFrom_transport (sym45M4443 : Magma (Fin 5)) sym45M4443_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4443_endo sym45.htr
    nosym45_Law1113

theorem Equation14_not_definableFrom_Equation4541 :
    ¬ Law14.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law14

theorem Equation477_not_definableFrom_Equation4541 :
    ¬ Law477.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law477

theorem Equation680_not_definableFrom_Equation4541 :
    ¬ Law680.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law680

theorem Equation692_not_definableFrom_Equation4541 :
    ¬ Law692.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law692

theorem Equation707_not_definableFrom_Equation4541 :
    ¬ Law707.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law707

theorem Equation870_not_definableFrom_Equation4541 :
    ¬ Law870.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law870

theorem Equation917_not_definableFrom_Equation4541 :
    ¬ Law917.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law917

theorem Equation978_not_definableFrom_Equation4541 :
    ¬ Law978.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law978

theorem Equation1113_not_definableFrom_Equation4541 :
    ¬ Law1113.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law1113

theorem Equation1276_not_definableFrom_Equation4541 :
    ¬ Law1276.DefinableFrom Law4541 :=
  not_definableFrom_transport (sym45M4541 : Magma (Fin 5)) sym45M4541_models
    sym45.E sym45.Einv sym45.rep sym45.tr sym45.hl sym45.hr sym45M4541_endo sym45.htr
    nosym45_Law1276
