import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All

/-!
# Recovering the square of an E873 magma from its left division

Write S(x)=M(x,x) for a source square and D for left division. E873 immediately
gives D(y,x)=M(S(x),S(y)). In particular D(x,x)=S²(x). A second diagonal
substitution gives the less obvious recovery formula S(x)=D(D(x,x),x).
Thus the source square is a two-operation term in division, even though a
uniform term for its inverse has not been found.

The two resulting identities are necessary image conditions, not an
unconditional characterization: the Boolean operation x AND NOT y satisfies
both but is not a left quasigroup. No catalogue characterization is registered.
-/
namespace Parastrophes.Eq873Division

def core {G : Type*} (D : Magma G) (x : G) := D.op (D.op x x) x

def Basis {G : Type*} (D : Magma G) : Prop :=
  (∀ x, D.op x (core D x) = x) ∧
  (∀ x y, D.op (core D x) (D.op y x) = core D y)

theorem division_formula {G : Type*} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation873 G M) (x y : G) :
    D.op y x = M.op (M.op x x) (M.op y y) := by
  have he := congrArg (D.op y) (h x y)
  simpa only [hd.2] using he

theorem core_eq_square {G : Type*} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation873 G M) (x : G) :
    core D x = M.op x x := by
  unfold core
  rw [division_formula M D hd h, division_formula M D hd h]
  exact (h (M.op x x) (M.op x x)).symm

theorem forward {G : Type*} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation873 G M) : Basis D := by
  constructor
  · intro x
    rw [core_eq_square M D hd h, hd.2]
  · intro x y
    rw [core_eq_square M D hd h, core_eq_square M D hd h,
      division_formula M D hd h x y, hd.2]

/-- The two identities become an exact characterization once left division
exists. This statement also works on infinite carriers. -/
theorem characterizes_leftQuasigroups {G : Type} (D : Magma G)
    (hq : IsSideQuasigroup .left D) : Basis D ↔ InImage Law873 .left D := by
  constructor
  · intro h
    classical
    let e (x : G) := Equiv.ofBijective (D.op x) (hq x)
    let M : Magma G := ⟨fun x y => (e x).symm y⟩
    have hd : IsDivision .left M D :=
      ⟨fun x y => (e x).symm_apply_apply y, fun x y => (e x).apply_symm_apply y⟩
    have hs (x : G) : M.op x x = core D x := by
      have he := congrArg (M.op x) (h.1 x)
      simpa only [hd.1] using he.symm
    have he : @Equation873 G M := by
      intro x y
      have hc := congrArg (fun z => M.op y (M.op (core D x) z)) (h.2 x y)
      simpa only [hd.1, hs] using hc
    exact ⟨M, (@Law873.models_iff G M).mpr he, hd⟩
  · rintro ⟨M, hm, hd⟩
    exact forward M D hd ((@Law873.models_iff G M).mp hm)

/-- Left cancellation turns the crossed identity into injectivity of the
recovered square. Finiteness is not needed for this step. -/
theorem core_injective {G : Type*} (D : Magma G)
    (hq : IsSideQuasigroup .left D) (h : Basis D) : Function.Injective (core D) := by
  intro x y he
  apply (hq x).1
  apply (hq (core D x)).1
  exact (h.2 x x).trans (by simpa only [he] using (h.2 y x).symm)

@[implicit_reducible] def booleanCounterexample : Magma Bool :=
  ⟨fun x y => x && !y⟩

theorem booleanCounterexample_basis : Basis booleanCounterexample := by
  unfold Basis core booleanCounterexample
  decide

theorem booleanCounterexample_not_image :
    ¬ InImage Law873 .left booleanCounterexample := by
  rintro ⟨M, _, hd⟩
  have hq := sideQuasigroup_of_division (division_symm hd)
  have he : false = true := (hq false).1 rfl
  exact Bool.noConfusion he

end Parastrophes.Eq873Division
