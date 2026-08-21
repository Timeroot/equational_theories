import equational_theories.Definability.Transport
import equational_theories.Equations.All

/-!
# Symmetry refutations: cyclic shift on Fin 5

The operations on the carrier invariant under this group, searched exhaustively. The search space
`Magma.transport` presents to `native_decide` is 3125 tuples -- one value per orbit on ordered pairs
-- of which only those passing the invariance test are real invariant operations.

`Magma.transport` and `Law.MagmaLaw.not_definableFrom_transport` do all the work; see
`Definability/Transport.lean`. Everything below is data and `decide`.
-/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-! ### cyclic shift on Fin 5 -/

namespace cyc5

/-- The 5 permutations of `Fin 5`, and their inverses. -/
def E : Fin 5 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![1, 2, 3, 4, 0], ![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], ![4, 0, 1, 2, 3]]

def Einv : Fin 5 → Fin 5 → Fin 5 := ![![0, 1, 2, 3, 4], ![4, 0, 1, 2, 3], ![3, 4, 0, 1, 2], ![2, 3, 4, 0, 1], ![1, 2, 3, 4, 0]]

/-- One ordered pair per orbit (5 of them), and for each pair the orbit it lies in
together with a permutation carrying that orbit's representative to it. -/
def rep : Fin 5 → Fin 5 × Fin 5 := ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]

def tr : Fin 5 → Fin 5 → Fin 5 × Fin 5 := fun x y ↦
  ![![(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)], ![(4, 1), (0, 1), (1, 1), (2, 1), (3, 1)], ![(3, 2), (4, 2), (0, 2), (1, 2), (2, 2)], ![(2, 3), (3, 3), (4, 3), (0, 3), (1, 3)], ![(1, 4), (2, 4), (3, 4), (4, 4), (0, 4)]] x y

theorem hl : ∀ i, Function.LeftInverse (Einv i) (E i) := by decide

theorem hr : ∀ i, Function.RightInverse (Einv i) (E i) := by decide

theorem htr : ∀ x y, E (tr x y).2 (rep (tr x y).1).1 = x ∧
    E (tr x y).2 (rep (tr x y).1).2 = y := by decide

end cyc5

/-! ### The refuted targets -/

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 14. -/
theorem nocyc5_Law14 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law14 := by
  simp only [Law14.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 313. -/
theorem nocyc5_Law313 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law313 := by
  simp only [Law313.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 477. -/
theorem nocyc5_Law477 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law477 := by
  simp only [Law477.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 680. -/
theorem nocyc5_Law680 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law680 := by
  simp only [Law680.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 692. -/
theorem nocyc5_Law692 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law692 := by
  simp only [Law692.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 1276. -/
theorem nocyc5_Law1276 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law1276 := by
  simp only [Law1276.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 1519. -/
theorem nocyc5_Law1519 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law1519 := by
  simp only [Law1519.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 3272. -/
theorem nocyc5_Law3272 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law3272 := by
  simp only [Law3272.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 3472. -/
theorem nocyc5_Law3472 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law3472 := by
  simp only [Law3472.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 3588. -/
theorem nocyc5_Law3588 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law3588 := by
  simp only [Law3588.models_iff]
  native_decide

/-- No cyc5-invariant operation on `Fin 5` satisfies equation 4273. -/
theorem nocyc5_Law4273 : ∀ v : Fin 5 → Fin 5,
    (∀ i, (Magma.mk (Magma.transport cyc5.E cyc5.tr v)).IsEndo (cyc5.E i)) →
    ¬ @satisfies _ (Fin 5) (Magma.mk (Magma.transport cyc5.E cyc5.tr v)) Law4273 := by
  simp only [Law4273.models_iff]
  native_decide

/-! ### The sources -/

/-- A model of equation 4293 on `Fin 5` invariant under cyc5. -/
@[reducible]
def cyc5M4293 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![0, 0, 0, 3, 4], ![0, 1, 1, 1, 4], ![0, 1, 2, 2, 2], ![3, 1, 2, 3, 3], ![4, 4, 2, 3, 4]] x y

theorem cyc5M4293_models : @satisfies _ (Fin 5) cyc5M4293 Law4293 :=
  (@Law4293.models_iff (Fin 5) cyc5M4293).mpr (by native_decide)

theorem cyc5M4293_endo : ∀ i, cyc5M4293.IsEndo (cyc5.E i) := by decide

/-- A model of equation 4415 on `Fin 5` invariant under cyc5. -/
@[reducible]
def cyc5M4415 : Magma (Fin 5) := Magma.mk fun x y ↦ ![![1, 1, 3, 1, 0], ![1, 2, 2, 4, 2], ![3, 2, 3, 3, 0], ![1, 4, 3, 4, 4], ![0, 2, 0, 4, 0]] x y

theorem cyc5M4415_models : @satisfies _ (Fin 5) cyc5M4415 Law4415 :=
  (@Law4415.models_iff (Fin 5) cyc5M4415).mpr (by native_decide)

theorem cyc5M4415_endo : ∀ i, cyc5M4415.IsEndo (cyc5.E i) := by decide

/-! ### The refutations -- 22 cells -/

theorem Equation14_not_definableFrom_Equation4293 :
    ¬ Law14.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law14

theorem Equation313_not_definableFrom_Equation4293 :
    ¬ Law313.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law313

theorem Equation477_not_definableFrom_Equation4293 :
    ¬ Law477.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law477

theorem Equation680_not_definableFrom_Equation4293 :
    ¬ Law680.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law680

theorem Equation692_not_definableFrom_Equation4293 :
    ¬ Law692.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law692

theorem Equation1276_not_definableFrom_Equation4293 :
    ¬ Law1276.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law1276

theorem Equation1519_not_definableFrom_Equation4293 :
    ¬ Law1519.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law1519

theorem Equation3272_not_definableFrom_Equation4293 :
    ¬ Law3272.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law3272

theorem Equation3472_not_definableFrom_Equation4293 :
    ¬ Law3472.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law3472

theorem Equation3588_not_definableFrom_Equation4293 :
    ¬ Law3588.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law3588

theorem Equation4273_not_definableFrom_Equation4293 :
    ¬ Law4273.DefinableFrom Law4293 :=
  not_definableFrom_transport (cyc5M4293 : Magma (Fin 5)) cyc5M4293_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4293_endo cyc5.htr
    nocyc5_Law4273

theorem Equation14_not_definableFrom_Equation4415 :
    ¬ Law14.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law14

theorem Equation313_not_definableFrom_Equation4415 :
    ¬ Law313.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law313

theorem Equation477_not_definableFrom_Equation4415 :
    ¬ Law477.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law477

theorem Equation680_not_definableFrom_Equation4415 :
    ¬ Law680.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law680

theorem Equation692_not_definableFrom_Equation4415 :
    ¬ Law692.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law692

theorem Equation1276_not_definableFrom_Equation4415 :
    ¬ Law1276.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law1276

theorem Equation1519_not_definableFrom_Equation4415 :
    ¬ Law1519.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law1519

theorem Equation3272_not_definableFrom_Equation4415 :
    ¬ Law3272.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law3272

theorem Equation3472_not_definableFrom_Equation4415 :
    ¬ Law3472.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law3472

theorem Equation3588_not_definableFrom_Equation4415 :
    ¬ Law3588.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law3588

theorem Equation4273_not_definableFrom_Equation4415 :
    ¬ Law4273.DefinableFrom Law4415 :=
  not_definableFrom_transport (cyc5M4415 : Magma (Fin 5)) cyc5M4415_models
    cyc5.E cyc5.Einv cyc5.rep cyc5.tr cyc5.hl cyc5.hr cyc5M4415_endo cyc5.htr
    nocyc5_Law4273
