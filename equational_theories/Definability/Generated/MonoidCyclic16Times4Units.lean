import equational_theories.Definability.EndomorphismFamilyCounting
import Mathlib.Algebra.Group.MinimalAxioms

/-! Complete left-translation families restricted by noninvertible endomorphisms. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma.MonoidCyclic16Times4Units
def A := Fin 16
instance : Fintype A := inferInstanceAs (Fintype (Fin 16))
instance : DecidableEq A := inferInstanceAs (DecidableEq (Fin 16))
instance (n : ℕ) : OfNat A n := inferInstanceAs (OfNat (Fin 16) n)
instance : Inhabited A := ⟨0⟩
def groupData : Array (Array A) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0], #[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1], #[3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2], #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3], #[5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4], #[6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5], #[7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6], #[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7], #[9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8], #[10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9], #[11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], #[12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], #[14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], #[15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
def inverseData : Array A := #[0, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]
instance : Add A := ⟨fun x y => (groupData.getD x.val #[]).getD y.val 0⟩
instance : Zero A := ⟨0⟩
instance : Neg A := ⟨fun x => inverseData.getD x.val 0⟩
instance : AddGroup A := AddGroup.ofLeftAxioms (by native_decide) (by native_decide) (by native_decide)
def mapData : Array (Array A) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[0, 3, 6, 9, 12, 15, 2, 5, 8, 11, 14, 1, 4, 7, 10, 13], #[0, 4, 8, 12, 0, 4, 8, 12, 0, 4, 8, 12, 0, 4, 8, 12], #[0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11], #[0, 7, 14, 5, 12, 3, 10, 1, 8, 15, 6, 13, 4, 11, 2, 9], #[0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 5, 14, 7], #[0, 11, 6, 1, 12, 7, 2, 13, 8, 3, 14, 9, 4, 15, 10, 5], #[0, 13, 10, 7, 4, 1, 14, 11, 8, 5, 2, 15, 12, 9, 6, 3], #[0, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], #[0, 12, 8, 4, 0, 12, 8, 4, 0, 12, 8, 4, 0, 12, 8, 4], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def mapFunction (i : Fin 11) (x : A) : A := (mapData.getD i.val #[]).getD x.val 0
theorem map_zero : ∀ i, mapFunction i 0 = 0 := by native_decide
theorem map_add : ∀ i x y, mapFunction i (x + y) = mapFunction i x + mapFunction i y := by native_decide
def maps (i : Fin 11) : A →+ A where
  toFun := mapFunction i
  map_zero' := map_zero i
  map_add' := map_add i

def valueData : Array (Array A) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 14, 0, 0, 0, 10, 0, 8, 0, 6, 0, 0, 0, 2, 0], #[0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 4, 0], #[0, 0, 10, 0, 0, 0, 14, 0, 8, 0, 2, 0, 0, 0, 6, 0], #[0, 0, 8, 0, 0, 0, 8, 0, 0, 0, 8, 0, 0, 0, 8, 0], #[0, 0, 6, 0, 0, 0, 2, 0, 8, 0, 14, 0, 0, 0, 10, 0], #[0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 12, 0], #[0, 0, 2, 0, 0, 0, 6, 0, 8, 0, 10, 0, 0, 0, 14, 0], #[0, 15, 0, 13, 12, 11, 0, 9, 0, 7, 0, 5, 4, 3, 0, 1], #[0, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], #[0, 15, 12, 13, 12, 11, 4, 9, 0, 7, 12, 5, 4, 3, 4, 1], #[0, 15, 10, 13, 12, 11, 14, 9, 8, 7, 2, 5, 4, 3, 6, 1], #[0, 15, 8, 13, 12, 11, 8, 9, 0, 7, 8, 5, 4, 3, 8, 1], #[0, 15, 6, 13, 12, 11, 2, 9, 8, 7, 14, 5, 4, 3, 10, 1], #[0, 15, 4, 13, 12, 11, 12, 9, 0, 7, 4, 5, 4, 3, 12, 1], #[0, 15, 2, 13, 12, 11, 6, 9, 8, 7, 10, 5, 4, 3, 14, 1], #[0, 14, 0, 10, 8, 6, 0, 2, 0, 14, 0, 10, 8, 6, 0, 2], #[0, 14, 14, 10, 8, 6, 10, 2, 8, 14, 6, 10, 8, 6, 2, 2], #[0, 14, 12, 10, 8, 6, 4, 2, 0, 14, 12, 10, 8, 6, 4, 2], #[0, 14, 10, 10, 8, 6, 14, 2, 8, 14, 2, 10, 8, 6, 6, 2], #[0, 14, 8, 10, 8, 6, 8, 2, 0, 14, 8, 10, 8, 6, 8, 2], #[0, 14, 6, 10, 8, 6, 2, 2, 8, 14, 14, 10, 8, 6, 10, 2], #[0, 14, 4, 10, 8, 6, 12, 2, 0, 14, 4, 10, 8, 6, 12, 2], #[0, 14, 2, 10, 8, 6, 6, 2, 8, 14, 10, 10, 8, 6, 14, 2], #[0, 13, 0, 7, 4, 1, 0, 11, 0, 5, 0, 15, 12, 9, 0, 3], #[0, 13, 14, 7, 4, 1, 10, 11, 8, 5, 6, 15, 12, 9, 2, 3], #[0, 13, 12, 7, 4, 1, 4, 11, 0, 5, 12, 15, 12, 9, 4, 3], #[0, 13, 10, 7, 4, 1, 14, 11, 8, 5, 2, 15, 12, 9, 6, 3], #[0, 13, 8, 7, 4, 1, 8, 11, 0, 5, 8, 15, 12, 9, 8, 3], #[0, 13, 6, 7, 4, 1, 2, 11, 8, 5, 14, 15, 12, 9, 10, 3], #[0, 13, 4, 7, 4, 1, 12, 11, 0, 5, 4, 15, 12, 9, 12, 3], #[0, 13, 2, 7, 4, 1, 6, 11, 8, 5, 10, 15, 12, 9, 14, 3], #[0, 12, 0, 4, 0, 12, 0, 4, 0, 12, 0, 4, 0, 12, 0, 4], #[0, 12, 14, 4, 0, 12, 10, 4, 8, 12, 6, 4, 0, 12, 2, 4], #[0, 12, 12, 4, 0, 12, 4, 4, 0, 12, 12, 4, 0, 12, 4, 4], #[0, 12, 10, 4, 0, 12, 14, 4, 8, 12, 2, 4, 0, 12, 6, 4], #[0, 12, 8, 4, 0, 12, 8, 4, 0, 12, 8, 4, 0, 12, 8, 4], #[0, 12, 6, 4, 0, 12, 2, 4, 8, 12, 14, 4, 0, 12, 10, 4], #[0, 12, 4, 4, 0, 12, 12, 4, 0, 12, 4, 4, 0, 12, 12, 4], #[0, 12, 2, 4, 0, 12, 6, 4, 8, 12, 10, 4, 0, 12, 14, 4], #[0, 11, 0, 1, 12, 7, 0, 13, 0, 3, 0, 9, 4, 15, 0, 5], #[0, 11, 14, 1, 12, 7, 10, 13, 8, 3, 6, 9, 4, 15, 2, 5], #[0, 11, 12, 1, 12, 7, 4, 13, 0, 3, 12, 9, 4, 15, 4, 5], #[0, 11, 10, 1, 12, 7, 14, 13, 8, 3, 2, 9, 4, 15, 6, 5], #[0, 11, 8, 1, 12, 7, 8, 13, 0, 3, 8, 9, 4, 15, 8, 5], #[0, 11, 6, 1, 12, 7, 2, 13, 8, 3, 14, 9, 4, 15, 10, 5], #[0, 11, 4, 1, 12, 7, 12, 13, 0, 3, 4, 9, 4, 15, 12, 5], #[0, 11, 2, 1, 12, 7, 6, 13, 8, 3, 10, 9, 4, 15, 14, 5], #[0, 10, 0, 14, 8, 2, 0, 6, 0, 10, 0, 14, 8, 2, 0, 6], #[0, 10, 14, 14, 8, 2, 10, 6, 8, 10, 6, 14, 8, 2, 2, 6], #[0, 10, 12, 14, 8, 2, 4, 6, 0, 10, 12, 14, 8, 2, 4, 6], #[0, 10, 10, 14, 8, 2, 14, 6, 8, 10, 2, 14, 8, 2, 6, 6], #[0, 10, 8, 14, 8, 2, 8, 6, 0, 10, 8, 14, 8, 2, 8, 6], #[0, 10, 6, 14, 8, 2, 2, 6, 8, 10, 14, 14, 8, 2, 10, 6], #[0, 10, 4, 14, 8, 2, 12, 6, 0, 10, 4, 14, 8, 2, 12, 6], #[0, 10, 2, 14, 8, 2, 6, 6, 8, 10, 10, 14, 8, 2, 14, 6], #[0, 9, 0, 11, 4, 13, 0, 15, 0, 1, 0, 3, 12, 5, 0, 7], #[0, 9, 14, 11, 4, 13, 10, 15, 8, 1, 6, 3, 12, 5, 2, 7], #[0, 9, 12, 11, 4, 13, 4, 15, 0, 1, 12, 3, 12, 5, 4, 7], #[0, 9, 10, 11, 4, 13, 14, 15, 8, 1, 2, 3, 12, 5, 6, 7], #[0, 9, 8, 11, 4, 13, 8, 15, 0, 1, 8, 3, 12, 5, 8, 7], #[0, 9, 6, 11, 4, 13, 2, 15, 8, 1, 14, 3, 12, 5, 10, 7], #[0, 9, 4, 11, 4, 13, 12, 15, 0, 1, 4, 3, 12, 5, 12, 7], #[0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 5, 14, 7], #[0, 8, 0, 8, 0, 8, 0, 8, 0, 8, 0, 8, 0, 8, 0, 8], #[0, 8, 14, 8, 0, 8, 10, 8, 8, 8, 6, 8, 0, 8, 2, 8], #[0, 8, 12, 8, 0, 8, 4, 8, 0, 8, 12, 8, 0, 8, 4, 8], #[0, 8, 10, 8, 0, 8, 14, 8, 8, 8, 2, 8, 0, 8, 6, 8], #[0, 8, 8, 8, 0, 8, 8, 8, 0, 8, 8, 8, 0, 8, 8, 8], #[0, 8, 6, 8, 0, 8, 2, 8, 8, 8, 14, 8, 0, 8, 10, 8], #[0, 8, 4, 8, 0, 8, 12, 8, 0, 8, 4, 8, 0, 8, 12, 8], #[0, 8, 2, 8, 0, 8, 6, 8, 8, 8, 10, 8, 0, 8, 14, 8], #[0, 7, 0, 5, 12, 3, 0, 1, 0, 15, 0, 13, 4, 11, 0, 9], #[0, 7, 14, 5, 12, 3, 10, 1, 8, 15, 6, 13, 4, 11, 2, 9], #[0, 7, 12, 5, 12, 3, 4, 1, 0, 15, 12, 13, 4, 11, 4, 9], #[0, 7, 10, 5, 12, 3, 14, 1, 8, 15, 2, 13, 4, 11, 6, 9], #[0, 7, 8, 5, 12, 3, 8, 1, 0, 15, 8, 13, 4, 11, 8, 9], #[0, 7, 6, 5, 12, 3, 2, 1, 8, 15, 14, 13, 4, 11, 10, 9], #[0, 7, 4, 5, 12, 3, 12, 1, 0, 15, 4, 13, 4, 11, 12, 9], #[0, 7, 2, 5, 12, 3, 6, 1, 8, 15, 10, 13, 4, 11, 14, 9], #[0, 6, 0, 2, 8, 14, 0, 10, 0, 6, 0, 2, 8, 14, 0, 10], #[0, 6, 14, 2, 8, 14, 10, 10, 8, 6, 6, 2, 8, 14, 2, 10], #[0, 6, 12, 2, 8, 14, 4, 10, 0, 6, 12, 2, 8, 14, 4, 10], #[0, 6, 10, 2, 8, 14, 14, 10, 8, 6, 2, 2, 8, 14, 6, 10], #[0, 6, 8, 2, 8, 14, 8, 10, 0, 6, 8, 2, 8, 14, 8, 10], #[0, 6, 6, 2, 8, 14, 2, 10, 8, 6, 14, 2, 8, 14, 10, 10], #[0, 6, 4, 2, 8, 14, 12, 10, 0, 6, 4, 2, 8, 14, 12, 10], #[0, 6, 2, 2, 8, 14, 6, 10, 8, 6, 10, 2, 8, 14, 14, 10], #[0, 5, 0, 15, 4, 9, 0, 3, 0, 13, 0, 7, 12, 1, 0, 11], #[0, 5, 14, 15, 4, 9, 10, 3, 8, 13, 6, 7, 12, 1, 2, 11], #[0, 5, 12, 15, 4, 9, 4, 3, 0, 13, 12, 7, 12, 1, 4, 11], #[0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11], #[0, 5, 8, 15, 4, 9, 8, 3, 0, 13, 8, 7, 12, 1, 8, 11], #[0, 5, 6, 15, 4, 9, 2, 3, 8, 13, 14, 7, 12, 1, 10, 11], #[0, 5, 4, 15, 4, 9, 12, 3, 0, 13, 4, 7, 12, 1, 12, 11], #[0, 5, 2, 15, 4, 9, 6, 3, 8, 13, 10, 7, 12, 1, 14, 11], #[0, 4, 0, 12, 0, 4, 0, 12, 0, 4, 0, 12, 0, 4, 0, 12], #[0, 4, 14, 12, 0, 4, 10, 12, 8, 4, 6, 12, 0, 4, 2, 12], #[0, 4, 12, 12, 0, 4, 4, 12, 0, 4, 12, 12, 0, 4, 4, 12], #[0, 4, 10, 12, 0, 4, 14, 12, 8, 4, 2, 12, 0, 4, 6, 12], #[0, 4, 8, 12, 0, 4, 8, 12, 0, 4, 8, 12, 0, 4, 8, 12], #[0, 4, 6, 12, 0, 4, 2, 12, 8, 4, 14, 12, 0, 4, 10, 12], #[0, 4, 4, 12, 0, 4, 12, 12, 0, 4, 4, 12, 0, 4, 12, 12], #[0, 4, 2, 12, 0, 4, 6, 12, 8, 4, 10, 12, 0, 4, 14, 12], #[0, 3, 0, 9, 12, 15, 0, 5, 0, 11, 0, 1, 4, 7, 0, 13], #[0, 3, 14, 9, 12, 15, 10, 5, 8, 11, 6, 1, 4, 7, 2, 13], #[0, 3, 12, 9, 12, 15, 4, 5, 0, 11, 12, 1, 4, 7, 4, 13], #[0, 3, 10, 9, 12, 15, 14, 5, 8, 11, 2, 1, 4, 7, 6, 13], #[0, 3, 8, 9, 12, 15, 8, 5, 0, 11, 8, 1, 4, 7, 8, 13], #[0, 3, 6, 9, 12, 15, 2, 5, 8, 11, 14, 1, 4, 7, 10, 13], #[0, 3, 4, 9, 12, 15, 12, 5, 0, 11, 4, 1, 4, 7, 12, 13], #[0, 3, 2, 9, 12, 15, 6, 5, 8, 11, 10, 1, 4, 7, 14, 13], #[0, 2, 0, 6, 8, 10, 0, 14, 0, 2, 0, 6, 8, 10, 0, 14], #[0, 2, 14, 6, 8, 10, 10, 14, 8, 2, 6, 6, 8, 10, 2, 14], #[0, 2, 12, 6, 8, 10, 4, 14, 0, 2, 12, 6, 8, 10, 4, 14], #[0, 2, 10, 6, 8, 10, 14, 14, 8, 2, 2, 6, 8, 10, 6, 14], #[0, 2, 8, 6, 8, 10, 8, 14, 0, 2, 8, 6, 8, 10, 8, 14], #[0, 2, 6, 6, 8, 10, 2, 14, 8, 2, 14, 6, 8, 10, 10, 14], #[0, 2, 4, 6, 8, 10, 12, 14, 0, 2, 4, 6, 8, 10, 12, 14], #[0, 2, 2, 6, 8, 10, 6, 14, 8, 2, 10, 6, 8, 10, 14, 14], #[0, 1, 0, 3, 4, 5, 0, 7, 0, 9, 0, 11, 12, 13, 0, 15], #[0, 1, 14, 3, 4, 5, 10, 7, 8, 9, 6, 11, 12, 13, 2, 15], #[0, 1, 12, 3, 4, 5, 4, 7, 0, 9, 12, 11, 12, 13, 4, 15], #[0, 1, 10, 3, 4, 5, 14, 7, 8, 9, 2, 11, 12, 13, 6, 15], #[0, 1, 8, 3, 4, 5, 8, 7, 0, 9, 8, 11, 12, 13, 8, 15], #[0, 1, 6, 3, 4, 5, 2, 7, 8, 9, 14, 11, 12, 13, 10, 15], #[0, 1, 4, 3, 4, 5, 12, 7, 0, 9, 4, 11, 12, 13, 12, 15], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
def values (i : Fin 128) (x : A) : A := (valueData.getD i.val #[]).getD x.val 0
def coordinateData : Array A := #[1, 2]
def coordinate (i : Fin 2) : A := coordinateData.getD i.val 0
def transportData : Array (Fin 2 × Fin 11) := #[(0, 10), (0, 0), (1, 0), (0, 1), (0, 2), (0, 3), (1, 1), (0, 4), (1, 2), (0, 5), (1, 3), (0, 6), (0, 9), (0, 7), (1, 4), (0, 8)]
def transport (x : A) := transportData.getD x.val (0, 0)
def row (p : Fin 2 → A) (x : A) : A := maps (transport x).2 (p (transport x).1)
def key (f : A → A) : ℕ := (Finset.univ : Finset (Fin 16)).sum (fun x => (f x).val * 16 ^ x.val)
def keyData : Array ℕ := #[0, 144121819673136640, 288243570358356992, 432347797845445120, 576469548530665472, 720591367935362560, 864695526702973952, 1008817346107671040, 1167646647790653680, 1311768467463790320, 1455890218149010672, 1599994445636098800, 1744116196321319152, 1888238015726016240, 2032342174493627632, 2176463993898324720, 2335293291268448480, 2479415110941585120, 2623536861626805472, 2767641089113893600, 2911762839799113952, 3055884659203811040, 3199988817971422432, 3344110637376119520, 3502938839529582800, 3647060659202719440, 3791182409887939792, 3935286637375027920, 4079408388060248272, 4223530207464945360, 4367634366232556752, 4511756185637253840, 4665800408420073664, 4809922228093210304, 4954043978778430656, 5098148206265518784, 5242269956950739136, 5386391776355436224, 5530495935123047616, 5674617754527744704, 5833445956682256560, 5977567776355393200, 6121689527040613552, 6265793754527701680, 6409915505212922032, 6554037324617619120, 6698141483385230512, 6842263302789927600, 6929035006122188960, 7073156825795325600, 7217278576480545952, 7361382803967634080, 7505504554652854432, 7649626374057551520, 7793730532825162912, 7937852352229860000, 8096399079423389840, 8240520899096526480, 8384642649781746832, 8528746877268834960, 8672868627954055312, 8816990447358752400, 8961094606126363792, 9105216425531060880, 9259542123273814144, 9403663942946950784, 9547785693632171136, 9691889921119259264, 9836011671804479616, 9980133491209176704, 10124237649976788096, 10268359469381485184, 10427188766752657520, 10571310586425794160, 10715432337111014512, 10859536564598102640, 11003658315283322992, 11147780134688020080, 11291884293455631472, 11436006112860328560, 11594552840053858400, 11738674659726995040, 11882796410412215392, 12026900637899303520, 12171022388584523872, 12315144207989220960, 12459248366756832352, 12603370186161529440, 12690141889493790800, 12834263709166927440, 12978385459852147792, 13122489687339235920, 13266611438024456272, 13410733257429153360, 13554837416196764752, 13698959235601461840, 13853283838127554624, 13997405657800691264, 14141527408485911616, 14285631635972999744, 14429753386658220096, 14573875206062917184, 14717979364830528576, 14862101184235225664, 15020649006646464560, 15164770826319601200, 15308892577004821552, 15452996804491909680, 15597118555177130032, 15741240374581827120, 15885344533349438512, 16029466352754135600, 16188294554907598880, 16332416374580735520, 16476538125265955872, 16620642352753044000, 16764764103438264352, 16908885922842961440, 17052990081610572832, 17197111901015269920, 17355941198385393680, 17500063018058530320, 17644184768743750672, 17788288996230838800, 17932410746916059152, 18076532566320756240, 18220636725088367632, 18364758544493064720]
def findKey (key lo hi : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let v := keyData.getD mid 0
      if key = v then mid
      else if key < v then findKey key lo mid fuel
      else findKey key (mid + 1) hi fuel
    else 0
def recover (f : A → A) : Fin 128 := ⟨findKey (key f) 0 128 9 % 128, Nat.mod_lt _ (by decide)⟩
def cover (p : Fin 2 → A) : Fin 128 := recover (row p)
theorem transport_correct : ∀ x, maps (transport x).2 (coordinate (transport x).1) = x := by native_decide
theorem cover_correct : ∀ p : Fin 2 → A,
    (∀ i x, maps i (row p x) = row p (maps i x)) → ∀ x, values (cover p) x = row p x := by native_decide
theorem recovery_correct : ∀ k, recover (values k) = k := by native_decide
theorem values_injective : Function.Injective values := by
  intro p q h
  have h := congrArg recover h
  simpa only [recovery_correct] using h
theorem values_commute : ∀ k i x, maps i (values k x) = values k (maps i x) := by native_decide
theorem values_coverage : ∀ f : A → A, (∀ i x, maps i (f x) = f (maps i x)) → ∃ k, values k = f :=
  Magma.EndomorphismFamily.function_coverage_of_coordinates maps values coordinate transport
    transport_correct cover cover_correct
@[implicit_reducible] def model (p : Fin 128) : Magma A := Magma.EndomorphismFamily.fam values p
theorem translations (p : Fin 128) (a : A) : (model p).IsEndo (Equiv.addLeft a) :=
  Magma.EndomorphismFamily.family_generators maps values values_commute p (.inl a)
theorem move_zero : ∀ a : A, Equiv.addLeft a 0 = a := by intro a; exact add_zero a

private def law828 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 2) (.Leaf 0))))⟩
private theorem count828 : Fintype.card {p : Fin 128 // PointTest (0 : A) (model p) law828} = 17 := by native_decide

private def law1026 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 0))) (.Leaf 1)))⟩
private theorem count1026 : Fintype.card {p : Fin 128 // PointTest (0 : A) (model p) law1026} = 16 := by native_decide

private def law1233 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 1)) (.Leaf 2)))⟩
private theorem count1233 : Fintype.card {p : Fin 128 // PointTest (0 : A) (model p) law1233} = 20 := by native_decide

private def law1235 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 2)) (.Leaf 1)))⟩
private theorem count1235 : Fintype.card {p : Fin 128 // PointTest (0 : A) (model p) law1235} = 20 := by native_decide

private def law1236 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 2)) (.Leaf 2)))⟩
private theorem count1236 : Fintype.card {p : Fin 128 // PointTest (0 : A) (model p) law1236} = 20 := by native_decide

end Magma.MonoidCyclic16Times4Units

open Magma.MonoidCyclic16Times4Units

theorem Equation1026_not_termStructuralFromFin_Equation1233_monoidCyclic16Times4Units : ¬ Law1026.TermStructuralFromFin Law1233 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.EndomorphismFamily.gen maps)
    model (Magma.EndomorphismFamily.family_injective values values_injective)
    (Magma.EndomorphismFamily.coverage maps values values_coverage)
    (Magma.EndomorphismFamily.family_generators maps values values_commute)
    (fun p => PointTest (0 : A) (model p) law1233)
    (fun p => PointTest (0 : A) (model p) law1026)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1233, count1026]
    decide

/-- info: 'Equation1026_not_termStructuralFromFin_Equation1233_monoidCyclic16Times4Units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cover_correct._native.native_decide.ax_1_1,
 instAddGroupA._native.native_decide.ax_1,
 instAddGroupA._native.native_decide.ax_2,
 instAddGroupA._native.native_decide.ax_3,
 map_add._native.native_decide.ax_1_1,
 map_zero._native.native_decide.ax_1_1,
 recovery_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_commute._native.native_decide.ax_1_1,
 count1026._native.native_decide.ax_1_1,
 count1233._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1026_not_termStructuralFromFin_Equation1233_monoidCyclic16Times4Units

theorem Equation828_not_termStructuralFromFin_Equation1235_monoidCyclic16Times4Units : ¬ Law828.TermStructuralFromFin Law1235 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.EndomorphismFamily.gen maps)
    model (Magma.EndomorphismFamily.family_injective values values_injective)
    (Magma.EndomorphismFamily.coverage maps values values_coverage)
    (Magma.EndomorphismFamily.family_generators maps values values_commute)
    (fun p => PointTest (0 : A) (model p) law1235)
    (fun p => PointTest (0 : A) (model p) law828)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count1235, count828]
    decide

/-- info: 'Equation828_not_termStructuralFromFin_Equation1235_monoidCyclic16Times4Units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cover_correct._native.native_decide.ax_1_1,
 instAddGroupA._native.native_decide.ax_1,
 instAddGroupA._native.native_decide.ax_2,
 instAddGroupA._native.native_decide.ax_3,
 map_add._native.native_decide.ax_1_1,
 map_zero._native.native_decide.ax_1_1,
 recovery_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_commute._native.native_decide.ax_1_1,
 count1235._native.native_decide.ax_1_1,
 count828._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation828_not_termStructuralFromFin_Equation1235_monoidCyclic16Times4Units

theorem Equation1026_not_termStructuralFromFin_Equation1235_monoidCyclic16Times4Units : ¬ Law1026.TermStructuralFromFin Law1235 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.EndomorphismFamily.gen maps)
    model (Magma.EndomorphismFamily.family_injective values values_injective)
    (Magma.EndomorphismFamily.coverage maps values values_coverage)
    (Magma.EndomorphismFamily.family_generators maps values values_commute)
    (fun p => PointTest (0 : A) (model p) law1235)
    (fun p => PointTest (0 : A) (model p) law1026)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1235, count1026]
    decide

/-- info: 'Equation1026_not_termStructuralFromFin_Equation1235_monoidCyclic16Times4Units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cover_correct._native.native_decide.ax_1_1,
 instAddGroupA._native.native_decide.ax_1,
 instAddGroupA._native.native_decide.ax_2,
 instAddGroupA._native.native_decide.ax_3,
 map_add._native.native_decide.ax_1_1,
 map_zero._native.native_decide.ax_1_1,
 recovery_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_commute._native.native_decide.ax_1_1,
 count1026._native.native_decide.ax_1_1,
 count1235._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1026_not_termStructuralFromFin_Equation1235_monoidCyclic16Times4Units

theorem Equation1026_not_termStructuralFromFin_Equation1236_monoidCyclic16Times4Units : ¬ Law1026.TermStructuralFromFin Law1236 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.EndomorphismFamily.gen maps)
    model (Magma.EndomorphismFamily.family_injective values values_injective)
    (Magma.EndomorphismFamily.coverage maps values values_coverage)
    (Magma.EndomorphismFamily.family_generators maps values values_commute)
    (fun p => PointTest (0 : A) (model p) law1236)
    (fun p => PointTest (0 : A) (model p) law1026)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1236, count1026]
    decide

/-- info: 'Equation1026_not_termStructuralFromFin_Equation1236_monoidCyclic16Times4Units' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 cover_correct._native.native_decide.ax_1_1,
 instAddGroupA._native.native_decide.ax_1,
 instAddGroupA._native.native_decide.ax_2,
 instAddGroupA._native.native_decide.ax_3,
 map_add._native.native_decide.ax_1_1,
 map_zero._native.native_decide.ax_1_1,
 recovery_correct._native.native_decide.ax_1_1,
 transport_correct._native.native_decide.ax_1_1,
 values_commute._native.native_decide.ax_1_1,
 count1026._native.native_decide.ax_1_1,
 count1236._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1026_not_termStructuralFromFin_Equation1236_monoidCyclic16Times4Units

