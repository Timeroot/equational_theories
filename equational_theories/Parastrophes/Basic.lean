import equational_theories.MagmaOp
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Questions about the actual division operations of a law

These predicates concern fixed parastrophes, not the existence of an arbitrary
operation satisfying a target law. `Characterizes` is an equality of model classes
among all magmas in the selected scope. `SingleEquation` quantifies over *all*
finite magma identities, not just the 4694 catalogue entries.

As elsewhere in this project, empty carriers are allowed. Their translations are
bijective. All terms are binary, parameter-free terms in the original operation.
-/
namespace Parastrophes
open Law FreeMagma

inductive Scope where
  | all | fin
  deriving DecidableEq, Repr, Inhabited

def Scope.Allows : Scope → Type → Prop
  | .all, _ => True
  | .fin, G => Finite G

inductive Side where
  | left | right
  deriving DecidableEq, Repr, Inhabited

def Side.swap : Side → Side
  | .left => .right
  | .right => .left

@[simp] theorem Side.swap_swap (s : Side) : s.swap.swap = s := by cases s <;> rfl

/-- Every row and column of the operation is a bijection. -/
def IsQuasigroup {G : Type*} (M : Magma G) : Prop :=
  (∀ x, Function.Bijective (M.op x)) ∧
  (∀ y, Function.Bijective (fun x => M.op x y))

/-- Bijective translations on one side only: rows for left, columns for right. -/
def IsSideQuasigroup {G : Type*} (side : Side) (M : Magma G) : Prop :=
  match side with
  | .left => ∀ x, Function.Bijective (M.op x)
  | .right => ∀ y, Function.Bijective (fun x => M.op x y)

/-- Every model has the indicated division; the other side is unrestricted. -/
def SideQuasigroupLaw (scope : Scope) (L : NatMagmaLaw) (side : Side) : Prop :=
  ∀ (G : Type) (M : Magma G), scope.Allows G → @satisfies _ G M L →
    IsSideQuasigroup side M

/-- `D` is exactly the indicated division operation of `M`, with both inverse laws. -/
def IsDivision {G : Type*} (s : Side) (M D : Magma G) : Prop :=
  match s with
  | .left => (∀ x y, M.op x (D.op x y) = y) ∧ (∀ x y, D.op x (M.op x y) = y)
  | .right => (∀ x y, M.op (D.op x y) y = x) ∧ (∀ x y, D.op (M.op x y) y = x)

def QuasigroupLaw (scope : Scope) (L : NatMagmaLaw) : Prop :=
  ∀ (G : Type) (M : Magma G), scope.Allows G → @satisfies _ G M L → IsQuasigroup M

/-- Membership in the actual parastrophic image of the source model class. -/
def InImage {G : Type} (L : NatMagmaLaw) (side : Side) (D : Magma G) : Prop :=
  ∃ M : Magma G, @satisfies _ G M L ∧ IsDivision side M D

/-- Exact characterization, including the converse and the absence of extra models lacking this division. -/
def Characterizes (scope : Scope) (L : NatMagmaLaw) (side : Side)
    (target : NatMagmaLaw) : Prop :=
  ∀ (G : Type) (D : Magma G), scope.Allows G →
    (@satisfies _ G D target ↔ InImage L side D)

/-- There exists a single identity, with any finite number of variables and operations. -/
def SingleEquation (scope : Scope) (L : NatMagmaLaw) (side : Side) : Prop :=
  ∃ target : NatMagmaLaw, Characterizes scope L side target

/-- Evaluate a parameter-free binary term in a specified magma. -/
@[implicit_reducible]
def termMagma {G : Type*} (M : Magma G) (t : FreeMagma (Fin 2)) : Magma G :=
  ⟨fun x y => @evalInMagma _ _ M (fun i => if i = 0 then x else y) t⟩

/-- One specified term recovers the division on every model in the selected scope. -/
def UniformTermWitness (scope : Scope) (L : NatMagmaLaw) (side : Side)
    (t : FreeMagma (Fin 2)) : Prop :=
  ∀ (G : Type) (M : Magma G), scope.Allows G → @satisfies _ G M L →
    IsDivision side M (termMagma M t)

/-- A single term works in every model. The existential is outside the model quantifier. -/
def UniformTermRecovery (scope : Scope) (L : NatMagmaLaw) (side : Side) : Prop :=
  ∃ t : FreeMagma (Fin 2), UniformTermWitness scope L side t

/-- Each model admits a term; the term may depend on the model. -/
def TermRecovery (scope : Scope) (L : NatMagmaLaw) (side : Side) : Prop :=
  ∀ (G : Type) (M : Magma G), scope.Allows G → @satisfies _ G M L →
    ∃ t : FreeMagma (Fin 2), IsDivision side M (termMagma M t)

theorem uniform_implies_term {scope L side}
    (h : UniformTermRecovery scope L side) : TermRecovery scope L side := by
  obtain ⟨t, ht⟩ := h
  exact fun G M hG hL => ⟨t, ht G M hG hL⟩

theorem quasigroup_finite {L} (h : QuasigroupLaw .all L) : QuasigroupLaw .fin L :=
  fun G M _ hL => h G M trivial hL

theorem characterizes_finite {L side target} (h : Characterizes .all L side target) :
    Characterizes .fin L side target := fun G M _ => h G M trivial

theorem singleEquation_finite {L side} (h : SingleEquation .all L side) :
    SingleEquation .fin L side := by
  obtain ⟨target, ht⟩ := h
  exact ⟨target, characterizes_finite ht⟩

theorem termRecovery_finite {L side} (h : TermRecovery .all L side) :
    TermRecovery .fin L side := fun G M _ hL => h G M trivial hL

theorem uniformTermRecovery_finite {L side} (h : UniformTermRecovery .all L side) :
    UniformTermRecovery .fin L side := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, fun G M _ hL => ht G M trivial hL⟩

/-- Opposite operation on the same carrier (no change of universe or cardinality). -/
@[implicit_reducible]
def opposite {G : Type*} (M : Magma G) : Magma G := ⟨fun x y => M.op y x⟩

@[simp] theorem opposite_opposite {G : Type*} (M : Magma G) : opposite (opposite M) = M := rfl

@[simp] theorem quasigroup_opposite {G : Type*} (M : Magma G) :
    IsQuasigroup (opposite M) ↔ IsQuasigroup M := by
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Left division of the opposite is the opposite of right division, and conversely. -/
theorem division_opposite {G : Type*} (side : Side) (M D : Magma G) :
    IsDivision side.swap (opposite M) (opposite D) ↔ IsDivision side M D := by
  cases side <;> simp only [Side.swap, IsDivision]
  all_goals exact ⟨fun h => ⟨fun x y => h.1 y x, fun x y => h.2 y x⟩,
    fun h => ⟨fun x y => h.1 y x, fun x y => h.2 y x⟩⟩

/-- The relation defining left or right division is its own inverse. -/
theorem division_symm {G : Type*} {side : Side} {M D : Magma G}
    (h : IsDivision side M D) : IsDivision side D M := by
  cases side <;> exact ⟨h.2, h.1⟩

private theorem eval_opposite {G : Type*} (M : Magma G) (t : FreeMagma Nat) (v : Nat → G) :
    @evalInMagma _ _ (opposite M) v t.dual = @evalInMagma _ _ M v t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => simpa only [FreeMagma.dual, evalInMagma, opposite] using congrArg₂ M.op ha hb

 theorem satisfies_opposite {G : Type*} (M : Magma G) (L : NatMagmaLaw) :
    @satisfies _ G (opposite M) L.dual ↔ @satisfies _ G M L := by
  simp only [satisfies, satisfiesPhi, MagmaLaw.dual, eval_opposite]

 theorem quasigroup_dual {scope L} (h : QuasigroupLaw scope L) :
    QuasigroupLaw scope L.dual := by
  intro G M hG hL
  apply (quasigroup_opposite M).mp
  apply h G (opposite M) hG
  have := (satisfies_opposite (opposite M) L).mp hL
  exact this

 theorem inImage_dual {G : Type} (L : NatMagmaLaw) (side : Side) (D : Magma G) :
    InImage L.dual side.swap (opposite D) ↔ InImage L side D := by
  constructor
  · rintro ⟨M, hL, hD⟩
    refine ⟨opposite M, ?_, ?_⟩
    · exact (satisfies_opposite (opposite M) L).mp hL
    · simpa only [Side.swap_swap, opposite_opposite] using
        (division_opposite side.swap M (opposite D)).mpr hD
  · rintro ⟨M, hL, hD⟩
    exact ⟨opposite M, (satisfies_opposite M L).mpr hL,
      (division_opposite side M D).mpr hD⟩

 theorem characterizes_dual {scope L side target} (h : Characterizes scope L side target) :
    Characterizes scope L.dual side.swap target.dual := by
  intro G D hG
  have hh := h G (opposite D) hG
  have hs := satisfies_opposite (opposite D) target
  have hi := inImage_dual L side (opposite D)
  exact hs.trans (hh.trans hi.symm)

 theorem singleEquation_dual {scope L side} (h : SingleEquation scope L side) :
    SingleEquation scope L.dual side.swap := by
  obtain ⟨target, ht⟩ := h
  exact ⟨target.dual, characterizes_dual ht⟩

/-- Mirror the operation tree and swap the two input variables. -/
def dualTerm (t : FreeMagma (Fin 2)) : FreeMagma (Fin 2) :=
  FreeMagma.fmapFreeMagma (fun i => if i = 0 then 1 else 0) t.dual

private theorem termMagma_dual {G : Type*} (M : Magma G) (t : FreeMagma (Fin 2)) :
    termMagma (opposite M) (dualTerm t) = opposite (termMagma M t) := by
  unfold termMagma opposite
  congr 1
  funext x y
  induction t with
  | Leaf i => fin_cases i <;> rfl
  | Fork a b ha hb =>
    change M.op _ _ = M.op _ _
    exact congrArg₂ M.op ha hb

 theorem uniformTermRecovery_dual {scope L side} (h : UniformTermRecovery scope L side) :
    UniformTermRecovery scope L.dual side.swap := by
  obtain ⟨t, ht⟩ := h
  refine ⟨dualTerm t, ?_⟩
  intro G M hG hL
  have hh := ht G (opposite M) hG ((satisfies_opposite (opposite M) L).mp hL)
  have hd := (division_opposite side (opposite M) (termMagma (opposite M) t)).mpr hh
  have he := termMagma_dual (opposite M) t
  rw [opposite_opposite] at he
  rw [he]
  exact hd

 theorem termRecovery_dual {scope L side} (h : TermRecovery scope L side) :
    TermRecovery scope L.dual side.swap := by
  intro G M hG hL
  obtain ⟨t, ht⟩ := h G (opposite M) hG ((satisfies_opposite (opposite M) L).mp hL)
  refine ⟨dualTerm t, ?_⟩
  have hd := (division_opposite side (opposite M) (termMagma (opposite M) t)).mpr ht
  have he := termMagma_dual (opposite M) t
  rw [opposite_opposite] at he
  rw [he]
  exact hd

/-- Having both division operations is equivalent to bijective translations. -/
theorem quasigroup_of_divisions {G : Type*} {M D E : Magma G}
    (hD : IsDivision .left M D) (hE : IsDivision .right M E) : IsQuasigroup M := by
  constructor
  · intro x
    exact ⟨fun a b hab => (hD.2 x a).symm.trans ((congrArg (D.op x) hab).trans (hD.2 x b)),
      fun y => ⟨D.op x y, hD.1 x y⟩⟩
  · intro y
    exact ⟨fun a b hab => (hE.2 a y).symm.trans ((congrArg (fun z => E.op z y) hab).trans (hE.2 b y)),
      fun x => ⟨E.op x y, hE.1 x y⟩⟩

/-- Term recovery of both divisions supplies both families of inverse translations. -/
theorem termRecovery_quasigroup {scope L} (hL : TermRecovery scope L .left)
    (hR : TermRecovery scope L .right) : QuasigroupLaw scope L := by
  intro G M hG hM
  obtain ⟨t, ht⟩ := hL G M hG hM
  obtain ⟨u, hu⟩ := hR G M hG hM
  exact quasigroup_of_divisions ht hu

private theorem left_division_quasigroup {G : Type*} {M D : Magma G}
    (hQ : IsQuasigroup M) (hD : IsDivision .left M D) : IsQuasigroup D := by
  constructor
  · intro x
    exact ⟨fun a b hab => (hD.1 x a).symm.trans ((congrArg (M.op x) hab).trans (hD.1 x b)),
      fun y => ⟨M.op x y, hD.2 x y⟩⟩
  · intro y
    constructor
    · intro a b hab
      apply (hQ.2 (D.op b y)).1
      change D.op a y = D.op b y at hab
      exact (congrArg (M.op a) hab.symm).trans ((hD.1 a y).trans (hD.1 b y).symm)
    · intro z
      obtain ⟨a, ha⟩ := (hQ.2 z).2 y
      exact ⟨a, (congrArg (D.op a) ha).symm.trans (hD.2 a z)⟩

/-- Every parastrophe of a quasigroup is again a quasigroup. -/
theorem division_quasigroup {G : Type*} {side : Side} {M D : Magma G}
    (hQ : IsQuasigroup M) (hD : IsDivision side M D) : IsQuasigroup D := by
  cases side with
  | left => exact left_division_quasigroup hQ hD
  | right =>
    apply (quasigroup_opposite D).mp
    exact left_division_quasigroup ((quasigroup_opposite M).mpr hQ)
      ((division_opposite .right M D).mpr hD)

 theorem characterizes_quasigroup {scope L side target}
    (h : Characterizes scope L side target) (hq : QuasigroupLaw scope L) :
    QuasigroupLaw scope target := by
  intro G D hG hT
  obtain ⟨M, hM, hD⟩ := (h G D hG).mp hT
  exact division_quasigroup (hq G M hG hM) hD

/-- Divisions are uniquely determined, so a recorded term denotes the actual parastrophe. -/
theorem division_unique {G : Type*} {side : Side} {M D E : Magma G}
    (hD : IsDivision side M D) (hE : IsDivision side M E) : D = E := by
  cases D with | mk d =>
    cases E with | mk e =>
      apply congrArg Magma.mk
      funext x y
      cases side with
      | left => exact (congrArg (d x) (hE.1 x y)).symm.trans (hD.2 x (e x y))
      | right => exact (congrArg (fun z => d z y) (hE.1 x y)).symm.trans (hD.2 (e x y) y)

/-- Ordinary implication in the selected carrier scope, for provenance-preserving transfer. -/
def ImpliesIn (scope : Scope) (L K : NatMagmaLaw) : Prop :=
  ∀ (G : Type) (M : Magma G), scope.Allows G → @satisfies _ G M L → @satisfies _ G M K

theorem quasigroup_of_implies {scope L K} (hI : ImpliesIn scope L K)
    (h : QuasigroupLaw scope K) : QuasigroupLaw scope L :=
  fun G M hG hL => h G M hG (hI G M hG hL)

theorem termRecovery_of_implies {scope L K side} (hI : ImpliesIn scope L K)
    (h : TermRecovery scope K side) : TermRecovery scope L side :=
  fun G M hG hL => h G M hG (hI G M hG hL)

theorem uniformTermRecovery_of_implies {scope L K side} (hI : ImpliesIn scope L K)
    (h : UniformTermRecovery scope K side) : UniformTermRecovery scope L side := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, fun G M hG hL => ht G M hG (hI G M hG hL)⟩

theorem singleEquation_of_equivalent {scope L K side} (hI : ImpliesIn scope L K)
    (hJ : ImpliesIn scope K L) (h : SingleEquation scope K side) :
    SingleEquation scope L side := by
  obtain ⟨target, ht⟩ := h
  refine ⟨target, ?_⟩
  intro G D hG
  refine (ht G D hG).trans ?_
  constructor <;> rintro ⟨M, hm, hD⟩
  · exact ⟨M, hJ G M hG hm, hD⟩
  · exact ⟨M, hI G M hG hm, hD⟩

/-- A division operation supplies exactly the required family of bijections. -/
theorem sideQuasigroup_of_division {G : Type*} {side : Side} {M D : Magma G}
    (h : IsDivision side M D) : IsSideQuasigroup side M := by
  cases side with
  | left => exact fun x => ⟨fun a b hab => (h.2 x a).symm.trans
      ((congrArg (D.op x) hab).trans (h.2 x b)), fun y => ⟨D.op x y, h.1 x y⟩⟩
  | right => exact fun y => ⟨fun a b hab => (h.2 a y).symm.trans
      ((congrArg (fun z => D.op z y) hab).trans (h.2 b y)), fun x => ⟨D.op x y, h.1 x y⟩⟩

/-- The other side survives a division exactly when it was available originally.
In particular a left-only quasigroup stays left-only after left division. -/
theorem division_otherSide_iff {G : Type*} {side : Side} {M D : Magma G}
    (h : IsDivision side M D) :
    IsSideQuasigroup side.swap D ↔ IsSideQuasigroup side.swap M := by
  have hm := sideQuasigroup_of_division h
  have hd := sideQuasigroup_of_division (division_symm h)
  cases side with
  | left => exact ⟨fun hD => (division_quasigroup ⟨hd, hD⟩ (division_symm h)).2,
      fun hM => (division_quasigroup ⟨hm, hM⟩ h).2⟩
  | right => exact ⟨fun hD => (division_quasigroup ⟨hD, hd⟩ (division_symm h)).1,
      fun hM => (division_quasigroup ⟨hM, hm⟩ h).1⟩

theorem quasigroup_side {scope L} (h : QuasigroupLaw scope L) (side : Side) :
    SideQuasigroupLaw scope L side := by
  intro G M hG hM
  cases side with
  | left => exact (h G M hG hM).1
  | right => exact (h G M hG hM).2

theorem sideQuasigroups_quasigroup {scope L}
    (hl : SideQuasigroupLaw scope L .left) (hr : SideQuasigroupLaw scope L .right) :
    QuasigroupLaw scope L := fun G M hG hM => ⟨hl G M hG hM, hr G M hG hM⟩

theorem sideQuasigroup_finite {L side} (h : SideQuasigroupLaw .all L side) :
    SideQuasigroupLaw .fin L side := fun G M _ hM => h G M trivial hM

theorem sideQuasigroup_dual {scope L side} (h : SideQuasigroupLaw scope L side) :
    SideQuasigroupLaw scope L.dual side.swap := by
  intro G M hG hM
  have hh := h G (opposite M) hG ((satisfies_opposite (opposite M) L).mp hM)
  cases side <;> exact hh

theorem sideQuasigroup_of_implies {scope L K side} (hi : ImpliesIn scope L K)
    (h : SideQuasigroupLaw scope K side) : SideQuasigroupLaw scope L side :=
  fun G M hG hM => h G M hG (hi G M hG hM)

theorem termRecovery_sideQuasigroup {scope L side} (h : TermRecovery scope L side) :
    SideQuasigroupLaw scope L side := by
  intro G M hG hM
  obtain ⟨t, ht⟩ := h G M hG hM
  exact sideQuasigroup_of_division ht

/-- Exact left/right images force that side, without implying the other side. -/
theorem characterizes_sideQuasigroup {scope L side target}
    (h : Characterizes scope L side target) : SideQuasigroupLaw scope target side := by
  intro G D hG hT
  obtain ⟨M, _, hD⟩ := (h G D hG).mp hT
  exact sideQuasigroup_of_division (division_symm hD)

/-- On a class possessing the division, an exact image can be inverted. -/
theorem characterizes_symm {scope L side K} (h : Characterizes scope L side K)
    (hs : SideQuasigroupLaw scope L side) : Characterizes scope K side L := by
  intro G M hG
  constructor
  · intro hM
    classical
    have hq := hs G M hG hM
    have hex : ∃ D : Magma G, IsDivision side M D := by
      cases side with
      | left =>
        refine ⟨⟨fun x y => (Equiv.ofBijective (M.op x) (hq x)).symm y⟩, ?_⟩
        exact ⟨fun x y => (Equiv.ofBijective (M.op x) (hq x)).apply_symm_apply y,
          fun x y => (Equiv.ofBijective (M.op x) (hq x)).symm_apply_apply y⟩
      | right =>
        refine ⟨⟨fun x y => (Equiv.ofBijective (fun z => M.op z y) (hq y)).symm x⟩, ?_⟩
        exact ⟨fun x y => (Equiv.ofBijective (fun z => M.op z y) (hq y)).apply_symm_apply x,
          fun x y => (Equiv.ofBijective (fun z => M.op z y) (hq y)).symm_apply_apply x⟩
    obtain ⟨D, hd⟩ := hex
    exact ⟨D, (h G D hG).mpr ⟨M, hM, hd⟩, division_symm hd⟩
  · rintro ⟨D, hD, hd⟩
    obtain ⟨N, hN, hn⟩ := (h G D hG).mp hD
    have he' : M = N := division_unique hd (division_symm hn)
    exact he'.symm ▸ hN

/-- An exact image preserves the other one-sided property, in either direction.
The source-side hypothesis ensures every source model belongs to the correspondence. -/
theorem characterizes_otherSide {scope L side K} (h : Characterizes scope L side K)
    (hs : SideQuasigroupLaw scope L side) :
    SideQuasigroupLaw scope L side.swap ↔ SideQuasigroupLaw scope K side.swap := by
  constructor
  · intro ho G D hG hK
    obtain ⟨M, hM, hd⟩ := (h G D hG).mp hK
    exact (division_otherSide_iff hd).mpr (ho G M hG hM)
  · intro ho G M hG hM
    obtain ⟨D, hD, hd⟩ := (characterizes_symm h hs G M hG).mp hM
    exact (division_otherSide_iff hd).mpr (ho G D hG hD)

/-- Right division of left division is opposite right division of multiplication. -/
theorem right_after_left {G : Type*} {M D R : Magma G}
    (hl : IsDivision .left M D) (hr : IsDivision .right M R) :
    IsDivision .right D (opposite R) := by
  constructor
  · intro x y
    have hh := hl.2 (R.op y x) x
    rw [hr.1 y x] at hh
    exact hh
  · intro x y
    have hh := hr.2 x (D.op x y)
    rw [hl.1 x y] at hh
    exact hh

/-- Left division of right division is opposite left division of multiplication. -/
theorem left_after_right {G : Type*} {M D R : Magma G}
    (hl : IsDivision .left M D) (hr : IsDivision .right M R) :
    IsDivision .left R (opposite D) := by
  constructor
  · intro x y
    have hh := hr.2 y (D.op y x)
    rw [hl.1 y x] at hh
    exact hh
  · intro x y
    have hh := hl.2 (R.op x y) y
    rw [hr.1 x y] at hh
    exact hh

end Parastrophes
