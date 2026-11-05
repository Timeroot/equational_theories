import equational_theories.Parastrophes.RotatedImages
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# A nine-element obstruction to the joined E714 image identity

The exact image is E464 plus left bijectivity. Write
F_y(x)=y*(x*(x*(x*y))) and G_z(x)=(z*x)*((z*x)*((z*x)*z)).
The candidate F_y(G_z(x))=x forces bijective rows but not E464: over
F₃[ε]/(ε²), let x*y=(-1+ε)(x+y)+1. Then F_y translates by 2ε and
G_z translates by ε. Their product is the identity although neither is.
-/
namespace Parastrophes.Eq714ImageCandidate
open Law

def triple {A : Type*} (M : Magma A) (x y : A) := M.op x (M.op x (M.op x y))
def F {A : Type*} (M : Magma A) (y x : A) := M.op y (triple M x y)
def G {A : Type*} (M : Magma A) (z x : A) := triple M (M.op z x) z
def Joined {A : Type*} (M : Magma A) : Prop := ∀ x y z, F M y (G M z x) = x

theorem joined_of_464 {A : Type} (M : Magma A) (h : @Equation464 A M)
    (hq : IsSideQuasigroup .left M) : Joined M := by
  have hf (y x : A) : F M y x = x := (h x y).symm
  have hg (z x : A) : G M z x = x := by
    apply (hq z).1
    exact hf z (M.op z x)
  intro x y z
  rw [hf, hg]

/-- The candidate already enforces row bijectivity. That does not suffice. -/
theorem joined_leftQuasigroup {A : Type} (M : Magma A) (h : Joined M) :
    IsSideQuasigroup .left M := by
  intro y
  constructor
  · intro a b he
    have ha := h a y y
    have hb := h b y y
    dsimp only [G] at ha hb
    rw [he] at ha
    exact ha.symm.trans hb
  · intro x
    exact ⟨triple M (G M y x) y, h x y y⟩

theorem image_equation464 {A : Type} (M : Magma A)
    (h : InImage Law714 .left M) : @Equation464 A M := by
  obtain ⟨N, hn, hd⟩ := h
  obtain ⟨P, hp, he⟩ :=
    (Catalogue.left_characterizes464_all_rotated A N trivial).mp hn
  have hPM : P = M := division_unique (division_symm he) hd
  exact hPM ▸ (@Law464.models_iff A P).mp hp

theorem joined_of_image {A : Type} (M : Magma A)
    (h : InImage Law714 .left M) : Joined M := by
  apply joined_of_464 M (image_equation464 M h)
  obtain ⟨N, _, hd⟩ := h
  exact sideQuasigroup_of_division (division_symm hd)

/-- Coordinates of (-1+ε)(x+y)+1, with ε²=0. -/
@[implicit_reducible] def magma : Magma (ZMod 3 × ZMod 3) :=
  ⟨fun x y => (-x.1-y.1+1, x.1+y.1-x.2-y.2)⟩

@[simp] theorem magma_op (x y : ZMod 3 × ZMod 3) :
    magma.op x y = (-x.1-y.1+1, x.1+y.1-x.2-y.2) := rfl

theorem F_formula (x y : ZMod 3 × ZMod 3) :
    F magma y x = (x.1, x.2+2) := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  have h3 : (3 : ZMod 3) = 0 := by decide
  apply Prod.ext <;> simp only [F, triple, magma_op]
  · ring
  · linear_combination (-a-c)*h3

theorem G_formula (x z : ZMod 3 × ZMod 3) :
    G magma z x = (x.1, x.2+1) := by
  rcases x with ⟨a,b⟩
  rcases z with ⟨c,d⟩
  have h3 : (3 : ZMod 3) = 0 := by decide
  apply Prod.ext <;> simp only [G, triple, magma_op]
  · ring
  · linear_combination -a*h3

theorem joined : Joined magma := by
  intro x y z
  rw [F_formula, G_formula]
  apply Prod.ext
  · rfl
  · change x.2+1+2=x.2
    have h3 : (3 : ZMod 3) = 0 := by decide
    linear_combination h3

theorem commutative : ∀ x y, magma.op x y = magma.op y x := by
  intro x y
  apply Prod.ext <;> simp only [magma_op] <;> ring

theorem quasigroup : IsQuasigroup magma := by
  have hq := joined_leftQuasigroup magma joined
  exact ⟨hq, fun y => by simpa only [commutative] using hq y⟩

theorem not_equation464 : ¬ @Equation464 (ZMod 3 × ZMod 3) magma := by
  intro h
  have he : (0,0) = F magma (0,0) (0,0) := h (0,0) (0,0)
  rw [F_formula] at he
  have hn : (0 : ZMod 3) = 2 := congrArg Prod.snd he
  exact (by decide : (0 : ZMod 3) ≠ 2) hn

theorem not_image : ¬ InImage Law714 .left magma :=
  fun h => not_equation464 (image_equation464 magma h)

/-- This refutes the converse even among finite commutative quasigroups. -/
theorem refutes_joined :
    ¬ (∀ (A : Type) [Finite A] (M : Magma A), Joined M ↔ InImage Law714 .left M) := by
  intro h
  exact not_image ((h _ magma).mp joined)

end Parastrophes.Eq714ImageCandidate
