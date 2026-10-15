import equational_theories.Definability.CloneTraps
import equational_theories.Definability.CloneShift
import equational_theories.Equations.All
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.DeriveFintype
/-! A six-element E960 recovery obstruction with a symbolic binary clone.

The carrier is two copies of `ZMod 3`. Each of 36 operations chooses its output
copy from one input, translates outside the odd/even input rectangle, and
translates or reflects inside it. The composition rule is proved by ring
arithmetic. Every recoverable candidate must be non-idempotent and fail
square-map equivariance; only twelve operations remain, and one explicit
assignment refutes each target law for each of those twelve.
-/
open Law Law.MagmaLaw
namespace SixElementCloneRecovery
abbrev Point := Bool × ZMod 3
structure Index where
  right : Bool
  outside : ZMod 3
  inside : ZMod 3
  reflected : Bool
  deriving Fintype, DecidableEq

def operation (i : Index) (x y : Point) : Point :=
  let (u,v) := if i.right then (x,y) else (y,x)
  (v.1, if u.1 && !v.1 then
    if i.reflected then u.2 - v.2 + i.inside else v.2 + i.inside
  else v.2 + i.outside)
@[implicit_reducible] def family (i : Index) : Magma Point := ⟨operation i⟩
@[implicit_reducible] def source : Magma Point := family ⟨true,1,1,true⟩
def compose (i j : Index) : Index :=
  ⟨j.right, j.outside + 1,
    if i.right = j.right then j.inside + 1 else i.outside - j.inside + 1,
    if i.right = j.right then j.reflected else !j.reflected⟩

theorem composition (i j : Index) (x y : Point) :
    operation (compose i j) x y = source.op (operation i x y) (operation j x y) := by
  change operation (compose i j) x y = operation ⟨true,1,1,true⟩ (operation i x y) (operation j x y)
  rcases i with ⟨ir,ik,il,ib⟩
  rcases j with ⟨jr,jk,jl,jb⟩
  rcases x with ⟨xp,xc⟩
  rcases y with ⟨yp,yc⟩
  cases ir <;> cases jr <;> cases xp <;> cases yp <;> cases jb <;>
    simp [compose, operation] <;> ring

theorem closed : source.IsCloneFamily family ⟨false,0,0,false⟩ ⟨true,0,0,false⟩ compose where
  fst := by
    intro x y
    change operation ⟨false,0,0,false⟩ x y = x
    rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩; cases b <;> cases c <;> simp [operation]
  snd := by
    intro x y
    change operation ⟨true,0,0,false⟩ x y = y
    rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩; cases b <;> cases c <;> simp [operation]
  comp := composition

theorem source_law : @Equation960 Point source := by
  intro x y z
  change x = operation ⟨true,1,1,true⟩ y (operation ⟨true,1,1,true⟩ (operation ⟨true,1,1,true⟩ z y) (operation ⟨true,1,1,true⟩ x x))
  rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩; rcases z with ⟨d,z⟩
  cases b <;> cases c <;> cases d <;>
    simp [operation] <;> ring_nf <;> norm_num <;> decide


def q (x : Point) : Point := (x.1, x.2 + 1)
def bad : Fin 12 → Index := ![⟨false,1,1,true⟩, ⟨true,1,1,true⟩, ⟨true,1,2,true⟩, ⟨false,2,0,true⟩, ⟨false,2,2,true⟩, ⟨false,1,2,true⟩, ⟨true,2,2,true⟩, ⟨false,2,1,true⟩, ⟨true,2,0,true⟩, ⟨true,2,1,true⟩, ⟨true,1,0,true⟩, ⟨false,1,0,true⟩]
def good (i : Index) : Prop := i.outside = 0 ∨ i.reflected = false
instance (i : Index) : Decidable (good i) := inferInstanceAs (Decidable (_ ∨ _))
def trap : Bool → (Point → Point → Point) → Prop
  | false => Magma.DiagFixed
  | true => Magma.Equivariant q
instance (b : Bool) (f : Point → Point → Point) : Decidable (trap b f) := by
  cases b <;> unfold trap <;> infer_instance

theorem trapped (i : Index) (h : good i) : ∃ b, trap b (family i).op := by
  rcases i with ⟨r,k,l,b⟩
  rcases h with hk | hb
  · refine ⟨false, ?_⟩
    change k = 0 at hk
    subst k
    change ∀ x, operation ⟨r,0,l,b⟩ x x = x
    rintro ⟨p,x⟩
    cases r <;> cases p <;> simp [operation]
  · refine ⟨true, ?_⟩
    change b = false at hb
    subst b
    change ∀ x y, operation ⟨r,k,l,false⟩ (q x) (q y) = q (operation ⟨r,k,l,false⟩ x y)
    rintro ⟨p,x⟩ ⟨s,y⟩
    cases r <;> cases p <;> cases s <;> simp [operation,q] <;> ring

theorem coverage : ∀ i, good i ∨ ∃ j, i = bad j := by decide
theorem source_untrapped : ∀ b, ¬ trap b source.op := by decide

theorem trap_invariant (b : Bool) (N : Magma Point) (h : trap b N.op) :
    N.IsCloneInvariant (trap b) := by
  cases b
  · exact Magma.DiagFixed.isCloneInvariant h
  · exact Magma.Equivariant.isCloneInvariant h

theorem obstruct {L : NatMagmaLaw}
    (h : ∀ j, ¬ @satisfies _ Point (family (bad j)) L) :
    ¬ L.TermStructuralFromFin Law960 := by
  apply not_termStructuralFromFin_of_cloneInv source
    ((@Law960.models_iff Point source).mpr source_law) closed trap_invariant source_untrapped
  intro i hi
  rcases coverage i with hg | ⟨j, rfl⟩
  · exact trapped i hg
  · exact False.elim (h j hi)

-- BEGIN GENERATED EXCLUSIONS (scripts/definability_six_element_clone.py)
private theorem exclude55 : ∀ j, ¬ @Equation55 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))

theorem Equation55_not_termStructuralFromFin_Equation960 :
    ¬ Law55.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude55 j ((@Law55.models_iff Point (family (bad j))).mp h))

private theorem exclude65 : ∀ j, ¬ @Equation65 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))

theorem Equation65_not_termStructuralFromFin_Equation960 :
    ¬ Law65.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude65 j ((@Law65.models_iff Point (family (bad j))).mp h))

private theorem exclude669 : ∀ j, ¬ @Equation669 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))

theorem Equation669_not_termStructuralFromFin_Equation960 :
    ¬ Law669.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude669 j ((@Law669.models_iff Point (family (bad j))).mp h))

private theorem exclude679 : ∀ j, ¬ @Equation679 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))

theorem Equation679_not_termStructuralFromFin_Equation960 :
    ¬ Law679.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude679 j ((@Law679.models_iff Point (family (bad j))).mp h))

private theorem exclude713 : ∀ j, ¬ @Equation713 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))

theorem Equation713_not_termStructuralFromFin_Equation960 :
    ¬ Law713.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude713 j ((@Law713.models_iff Point (family (bad j))).mp h))

private theorem exclude825 : ∀ j, ¬ @Equation825 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))

theorem Equation825_not_termStructuralFromFin_Equation960 :
    ¬ Law825.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude825 j ((@Law825.models_iff Point (family (bad j))).mp h))

private theorem exclude845 : ∀ j, ¬ @Equation845 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))

theorem Equation845_not_termStructuralFromFin_Equation960 :
    ¬ Law845.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude845 j ((@Law845.models_iff Point (family (bad j))).mp h))

private theorem exclude872 : ∀ j, ¬ @Equation872 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))

theorem Equation872_not_termStructuralFromFin_Equation960 :
    ¬ Law872.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude872 j ((@Law872.models_iff Point (family (bad j))).mp h))

private theorem exclude1434 : ∀ j, ¬ @Equation1434 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))

theorem Equation1434_not_termStructuralFromFin_Equation960 :
    ¬ Law1434.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude1434 j ((@Law1434.models_iff Point (family (bad j))).mp h))

private theorem exclude1451 : ∀ j, ¬ @Equation1451 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))

theorem Equation1451_not_termStructuralFromFin_Equation960 :
    ¬ Law1451.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude1451 j ((@Law1451.models_iff Point (family (bad j))).mp h))

private theorem exclude1525 : ∀ j, ¬ @Equation1525 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))

theorem Equation1525_not_termStructuralFromFin_Equation960 :
    ¬ Law1525.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude1525 j ((@Law1525.models_iff Point (family (bad j))).mp h))

private theorem exclude3315 : ∀ j, ¬ @Equation3315 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))

theorem Equation3315_not_termStructuralFromFin_Equation960 :
    ¬ Law3315.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude3315 j ((@Law3315.models_iff Point (family (bad j))).mp h))

private theorem exclude3316 : ∀ j, ¬ @Equation3316 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))

theorem Equation3316_not_termStructuralFromFin_Equation960 :
    ¬ Law3316.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude3316 j ((@Law3316.models_iff Point (family (bad j))).mp h))

private theorem exclude3318 : ∀ j, ¬ @Equation3318 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))

theorem Equation3318_not_termStructuralFromFin_Equation960 :
    ¬ Law3318.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude3318 j ((@Law3318.models_iff Point (family (bad j))).mp h))

private theorem exclude3319 : ∀ j, ¬ @Equation3319 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))

theorem Equation3319_not_termStructuralFromFin_Equation960 :
    ¬ Law3319.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude3319 j ((@Law3319.models_iff Point (family (bad j))).mp h))

private theorem exclude3518 : ∀ j, ¬ @Equation3518 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))

theorem Equation3518_not_termStructuralFromFin_Equation960 :
    ¬ Law3518.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude3518 j ((@Law3518.models_iff Point (family (bad j))).mp h))

private theorem exclude3519 : ∀ j, ¬ @Equation3519 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))

theorem Equation3519_not_termStructuralFromFin_Equation960 :
    ¬ Law3519.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude3519 j ((@Law3519.models_iff Point (family (bad j))).mp h))

private theorem exclude3521 : ∀ j, ¬ @Equation3521 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))

theorem Equation3521_not_termStructuralFromFin_Equation960 :
    ¬ Law3521.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude3521 j ((@Law3521.models_iff Point (family (bad j))).mp h))

private theorem exclude3522 : ∀ j, ¬ @Equation3522 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (false, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))

theorem Equation3522_not_termStructuralFromFin_Equation960 :
    ¬ Law3522.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude3522 j ((@Law3522.models_iff Point (family (bad j))).mp h))

private theorem exclude4275 : ∀ j, ¬ @Equation4275 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 1) : Point) ≠ (true, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (true, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (true, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (true, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (true, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (true, 1)) (h (false, 0) (true, 0))

theorem Equation4275_not_termStructuralFromFin_Equation960 :
    ¬ Law4275.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude4275 j ((@Law4275.models_iff Point (family (bad j))).mp h))

private theorem exclude4320 : ∀ j, ¬ @Equation4320 Point (family (bad j)) := by
  intro j h
  fin_cases j
  · exact (by decide : ((false, 2) : Point) ≠ (true, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (true, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (true, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (true, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 0)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (true, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 2) : Point) ≠ (false, 1)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 0) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (false, 2)) (h (false, 0) (true, 0))
  · exact (by decide : ((false, 1) : Point) ≠ (true, 1)) (h (false, 0) (true, 0))

theorem Equation4320_not_termStructuralFromFin_Equation960 :
    ¬ Law4320.TermStructuralFromFin Law960 :=
  obstruct (fun j h => exclude4320 j ((@Law4320.models_iff Point (family (bad j))).mp h))

end SixElementCloneRecovery

/-- info: 'SixElementCloneRecovery.Equation55_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation55_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation65_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation65_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation669_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation669_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation679_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation679_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation713_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation713_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation825_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation825_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation845_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation845_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation872_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation872_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation1434_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation1434_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation1451_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation1451_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation1525_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation1525_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation3315_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation3315_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation3316_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation3316_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation3318_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation3318_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation3319_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation3319_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation3518_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation3518_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation3519_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation3519_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation3521_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation3521_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation3522_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation3522_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation4275_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation4275_not_termStructuralFromFin_Equation960

/-- info: 'SixElementCloneRecovery.Equation4320_not_termStructuralFromFin_Equation960' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SixElementCloneRecovery.Equation4320_not_termStructuralFromFin_Equation960
