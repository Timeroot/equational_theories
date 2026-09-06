import equational_theories.Definability.LinearIntModels

/-!
# The cover of the five integer models

The sixteen non-definability facts that `Definability/LinearIntModels.lean` contributes to the open
board. Every one of them has an integrality obstruction at its heart, so none is reachable by the
`ZMod` sweep: the targets `332`, `3342`, `3545` and `4343` all admit `α = β = 1 / 2`, and the target
`3558` admits `β` a square root of a unit, whenever those exist in the ring.

The statements refute `TermDefinableFrom`, and only over all magmas — the witnesses are infinite,
and a clone argument bounds terms rather than formulas.
-/

open Law.MagmaLaw

/-! ### `lin (-1) (-1)`, modulus `3` -/

theorem Equation332_not_termDefinableFrom_Equation492 :
    ¬ Law332.TermDefinableFrom Law492 :=
  liA_cert ((@Law492.models_iff ℤ (Magma.lin (-1 : ℤ) (-1))).mpr liA_sat.1)
    fun op hop h ↦ Magma.linShift_not_332 (c := 3) (fun g ↦ by omega) op hop
      ((@Law332.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation332_not_termDefinableFrom_Equation3364 :
    ¬ Law332.TermDefinableFrom Law3364 :=
  liA_cert ((@Law3364.models_iff ℤ (Magma.lin (-1 : ℤ) (-1))).mpr liA_sat.2)
    fun op hop h ↦ Magma.linShift_not_332 (c := 3) (fun g ↦ by omega) op hop
      ((@Law332.models_iff ℤ (Magma.mk op)).mp h)

/-! ### `lin (-2) (-2)`, modulus `5` -/

theorem Equation332_not_termDefinableFrom_Equation43 :
    ¬ Law332.TermDefinableFrom Law43 :=
  liB_cert ((@Law43.models_iff ℤ (Magma.lin (-2 : ℤ) (-2))).mpr liB_sat)
    fun op hop h ↦ Magma.linShift_not_332 (c := 5) (fun g ↦ by omega) op hop
      ((@Law332.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation43 :
    ¬ Law3342.TermDefinableFrom Law43 :=
  liB_cert ((@Law43.models_iff ℤ (Magma.lin (-2 : ℤ) (-2))).mpr liB_sat)
    fun op hop h ↦ Magma.linShift_not_3342 (c := 5) (fun g ↦ by omega) (fun g ↦ by omega) op hop
      ((@Law3342.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation43 :
    ¬ Law3545.TermDefinableFrom Law43 :=
  liB_cert ((@Law43.models_iff ℤ (Magma.lin (-2 : ℤ) (-2))).mpr liB_sat)
    fun op hop h ↦ Magma.linShift_not_3545 (c := 5) (fun g ↦ by omega) (fun g ↦ by omega) op hop
      ((@Law3545.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4343_not_termDefinableFrom_Equation43 :
    ¬ Law4343.TermDefinableFrom Law43 :=
  liB_cert ((@Law43.models_iff ℤ (Magma.lin (-2 : ℤ) (-2))).mpr liB_sat)
    fun op hop h ↦ Magma.linShift_not_4343 (c := 5) (fun g ↦ by omega) (fun g ↦ by omega) op hop
      ((@Law4343.models_iff ℤ (Magma.mk op)).mp h)

/-! ### `lin 4 2`, modulus `5` -/

theorem Equation332_not_termDefinableFrom_Equation4321 :
    ¬ Law332.TermDefinableFrom Law4321 :=
  liC_cert ((@Law4321.models_iff ℤ (Magma.lin (4 : ℤ) 2)).mpr liC_sat.1)
    fun op hop h ↦ Magma.linShift_not_332 (c := 5) (fun g ↦ by omega) op hop
      ((@Law332.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation4321 :
    ¬ Law3342.TermDefinableFrom Law4321 :=
  liC_cert ((@Law4321.models_iff ℤ (Magma.lin (4 : ℤ) 2)).mpr liC_sat.1)
    fun op hop h ↦ Magma.linShift_not_3342 (c := 5) (fun g ↦ by omega) (fun g ↦ by omega) op hop
      ((@Law3342.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation4321 :
    ¬ Law3545.TermDefinableFrom Law4321 :=
  liC_cert ((@Law4321.models_iff ℤ (Magma.lin (4 : ℤ) 2)).mpr liC_sat.1)
    fun op hop h ↦ Magma.linShift_not_3545 (c := 5) (fun g ↦ by omega) (fun g ↦ by omega) op hop
      ((@Law3545.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4343_not_termDefinableFrom_Equation4321 :
    ¬ Law4343.TermDefinableFrom Law4321 :=
  liC_cert ((@Law4321.models_iff ℤ (Magma.lin (4 : ℤ) 2)).mpr liC_sat.1)
    fun op hop h ↦ Magma.linShift_not_4343 (c := 5) (fun g ↦ by omega) (fun g ↦ by omega) op hop
      ((@Law4343.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3558_not_termDefinableFrom_Equation4369 :
    ¬ Law3558.TermDefinableFrom Law4369 :=
  liC_cert ((@Law4369.models_iff ℤ (Magma.lin (4 : ℤ) 2)).mpr liC_sat.2)
    fun op hop h ↦ Magma.linShift_not_3558 (c := 5) (fun g ↦ by omega) op hop
      ((@Law3558.models_iff ℤ (Magma.mk op)).mp h)

/-! ### `lin (-4) (-2)`, modulus `7` -/

theorem Equation332_not_termDefinableFrom_Equation4293 :
    ¬ Law332.TermDefinableFrom Law4293 :=
  liD_cert ((@Law4293.models_iff ℤ (Magma.lin (-4 : ℤ) (-2))).mpr liD_sat)
    fun op hop h ↦ Magma.linShift_not_332 (c := 7) (fun g ↦ by omega) op hop
      ((@Law332.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3342_not_termDefinableFrom_Equation4293 :
    ¬ Law3342.TermDefinableFrom Law4293 :=
  liD_cert ((@Law4293.models_iff ℤ (Magma.lin (-4 : ℤ) (-2))).mpr liD_sat)
    fun op hop h ↦ Magma.linShift_not_3342 (c := 7) (fun g ↦ by omega) (fun g ↦ by omega) op hop
      ((@Law3342.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation3545_not_termDefinableFrom_Equation4293 :
    ¬ Law3545.TermDefinableFrom Law4293 :=
  liD_cert ((@Law4293.models_iff ℤ (Magma.lin (-4 : ℤ) (-2))).mpr liD_sat)
    fun op hop h ↦ Magma.linShift_not_3545 (c := 7) (fun g ↦ by omega) (fun g ↦ by omega) op hop
      ((@Law3545.models_iff ℤ (Magma.mk op)).mp h)

theorem Equation4343_not_termDefinableFrom_Equation4293 :
    ¬ Law4343.TermDefinableFrom Law4293 :=
  liD_cert ((@Law4293.models_iff ℤ (Magma.lin (-4 : ℤ) (-2))).mpr liD_sat)
    fun op hop h ↦ Magma.linShift_not_4343 (c := 7) (fun g ↦ by omega) (fun g ↦ by omega) op hop
      ((@Law4343.models_iff ℤ (Magma.mk op)).mp h)

/-! ### `lin (-4) 2`, modulus `3` -/

theorem Equation332_not_termDefinableFrom_Equation4343 :
    ¬ Law332.TermDefinableFrom Law4343 :=
  liE_cert ((@Law4343.models_iff ℤ (Magma.lin (-4 : ℤ) 2)).mpr liE_sat)
    fun op hop h ↦ Magma.linShift_not_332 (c := 3) (fun g ↦ by omega) op hop
      ((@Law332.models_iff ℤ (Magma.mk op)).mp h)
