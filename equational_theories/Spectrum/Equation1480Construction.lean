import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status
import equational_theories.Equations.All
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

/-! Explicit core-and-pairs constructions for every E1480 order at least four. -/
open Classical
namespace Spectrum.Construction1480

abbrev EvenCarrier (Q : Type*) := Fin 4 ⊕ (Q × Bool)
abbrev OddCarrier (Q : Type*) := Fin 5 ⊕ (Q × Bool)

def evenCore (x y : Fin 4) : Fin 4 :=
  ![![3,3,2,2], ![1,1,0,2], ![3,3,2,2], ![1,1,0,0]] x y

noncomputable def evenOp {Q : Type*} : EvenCarrier Q → EvenCarrier Q → EvenCarrier Q
  | .inl x, .inl y => .inl (evenCore x y)
  | .inl x, .inr (_,false) => .inl (![2,1,2,1] x)
  | .inl _, .inr (j,true) => .inr (j,false)
  | .inr (i,_), .inl y =>
    if y = 0 ∨ y = 3 then .inr (i,true) else .inl (if y = 1 then 3 else 0)
  | .inr (i,a), .inr (j,false) =>
    if i = j then .inl (if a then 1 else 3) else .inr (i,true)
  | .inr (i,_), .inr (j,true) =>
    if i = j then .inr (i,true) else .inr (j,false)

def oddCore (x y : Fin 5) : Fin 5 :=
  ![![4,4,4,3,3], ![2,1,1,0,2], ![4,4,4,0,0], ![2,4,4,3,3], ![2,1,1,0,2]] x y

noncomputable def oddOp {Q : Type*} : OddCarrier Q → OddCarrier Q → OddCarrier Q
  | .inl x, .inl y => .inl (oddCore x y)
  | .inl x, .inr (_,false) => .inl (![3,1,0,4,1] x)
  | .inl _, .inr (j,true) => .inr (j,false)
  | .inr (i,_), .inl y =>
    if y = 0 ∨ y = 4 then .inr (i,true) else .inl (if y = 3 then 0 else 4)
  | .inr (i,false), .inr (j,false) => if i = j then .inl 4 else .inr (i,true)
  | .inr (_,true), .inr (_,false) => .inl 0
  | .inr (i,_), .inr (j,true) =>
    if i = j then .inr (i,true) else .inr (j,false)

set_option maxHeartbeats 4000000 in
theorem even_law {Q : Type*} (x y z : EvenCarrier Q) :
    evenOp (evenOp y x) (evenOp x (evenOp x z)) = x := by
  rcases x with x | ⟨x,bx⟩ <;>
    rcases y with y | ⟨y,byy⟩ <;>
    rcases z with z | ⟨z,bz⟩
  all_goals try fin_cases x
  all_goals try fin_cases y
  all_goals try fin_cases z
  all_goals try cases bx
  all_goals try cases byy
  all_goals try cases bz
  all_goals simp [evenOp, evenCore]
  all_goals split_ifs <;> simp_all

set_option maxHeartbeats 4000000 in
theorem odd_law {Q : Type*} (x y z : OddCarrier Q) :
    oddOp (oddOp y x) (oddOp x (oddOp x z)) = x := by
  rcases x with x | ⟨x,bx⟩ <;>
    rcases y with y | ⟨y,byy⟩ <;>
    rcases z with z | ⟨z,bz⟩
  all_goals try fin_cases x
  all_goals try fin_cases y
  all_goals try fin_cases z
  all_goals try cases bx
  all_goals try cases byy
  all_goals try cases bz
  all_goals simp [oddOp, oddCore]
  all_goals split_ifs <;> simp_all

theorem even_models (m : ℕ) : Law1480.HasModel (4+2*m) := by
  apply Law.MagmaLaw.hasModel_of_card (G := EvenCarrier (Fin m)) ⟨evenOp⟩
  · exact (@Law1480.models_iff _ ⟨evenOp⟩).mpr (fun x y z => (even_law x y z).symm)
  · simp [EvenCarrier, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm]

theorem odd_models (m : ℕ) : Law1480.HasModel (5+2*m) := by
  apply Law.MagmaLaw.hasModel_of_card (G := OddCarrier (Fin m)) ⟨oddOp⟩
  · exact (@Law1480.models_iff _ ⟨oddOp⟩).mpr (fun x y z => (odd_law x y z).symm)
  · simp [OddCarrier, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm]

spectrum_assert even_models complete
spectrum_assert odd_models complete
end Spectrum.Construction1480
