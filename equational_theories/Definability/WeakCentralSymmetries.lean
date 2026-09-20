import equational_theories.Definability.WeakCentralRelations

/-! The five generators of the free-orbit symmetry group fix the seventeen
small points, commute with rotation, and preserve each compatible relation.
This is not a proof of lexicographic normalization or of a SAT exclusion. -/

namespace Magma.WeakCentralSymmetries
open Magma.WeakCentralSource Magma.WeakCentralRelations
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def small : Fin 17 → Fin 32 := ![0, 5, 9, 10, 11, 13, 15, 18, 20, 21, 22, 23, 26, 27, 29, 30, 31]
def forward (i : Fin 5) (x : Fin 32) : Fin 32 :=
  match i.val, x.val with
  | 0, 1 => 2
  | 0, 2 => 4
  | 0, 4 => 8
  | 0, 8 => 16
  | 0, 16 => 1
  | 1, 3 => 6
  | 1, 6 => 12
  | 1, 12 => 24
  | 1, 17 => 3
  | 1, 24 => 17
  | 2, 7 => 14
  | 2, 14 => 28
  | 2, 19 => 7
  | 2, 25 => 19
  | 2, 28 => 25
  | 3, 1 => 3
  | 3, 2 => 6
  | 3, 3 => 1
  | 3, 4 => 12
  | 3, 6 => 2
  | 3, 8 => 24
  | 3, 12 => 4
  | 3, 16 => 17
  | 3, 17 => 16
  | 3, 24 => 8
  | 4, 3 => 7
  | 4, 6 => 14
  | 4, 7 => 3
  | 4, 12 => 28
  | 4, 14 => 6
  | 4, 17 => 19
  | 4, 19 => 17
  | 4, 24 => 25
  | 4, 25 => 24
  | 4, 28 => 12
  | _, _ => x
def backward (i : Fin 5) (x : Fin 32) : Fin 32 :=
  match i.val, x.val with
  | 0, 1 => 16
  | 0, 2 => 1
  | 0, 4 => 2
  | 0, 8 => 4
  | 0, 16 => 8
  | 1, 3 => 17
  | 1, 6 => 3
  | 1, 12 => 6
  | 1, 17 => 24
  | 1, 24 => 12
  | 2, 7 => 19
  | 2, 14 => 7
  | 2, 19 => 25
  | 2, 25 => 28
  | 2, 28 => 14
  | 3, 1 => 3
  | 3, 2 => 6
  | 3, 3 => 1
  | 3, 4 => 12
  | 3, 6 => 2
  | 3, 8 => 24
  | 3, 12 => 4
  | 3, 16 => 17
  | 3, 17 => 16
  | 3, 24 => 8
  | 4, 3 => 7
  | 4, 6 => 14
  | 4, 7 => 3
  | 4, 12 => 28
  | 4, 14 => 6
  | 4, 17 => 19
  | 4, 19 => 17
  | 4, 24 => 25
  | 4, 25 => 24
  | 4, 28 => 12
  | _, _ => x

theorem inverse : ∀ i x,
    backward i (forward i x) = x ∧ forward i (backward i x) = x := by decide

def perm (i : Fin 5) : Equiv.Perm (Fin 32) where
  toFun := forward i
  invFun := backward i
  left_inv x := (inverse i x).1
  right_inv x := (inverse i x).2

theorem fixes_small : ∀ i j, perm i (small j) = small j := by decide

theorem commutes_rotation : ∀ i x,
    perm i (rotation x) = rotation (perm i x) := by decide

theorem relation_images : ∀ i j, ∀ a ∈ pairs j,
    (perm i a.1, perm i a.2) ∈ pairs j ∧
    ((perm i).symm a.1, (perm i).symm a.2) ∈ pairs j := by native_decide

def relabel {G : Type} (f : G → G → G) (p : Equiv.Perm G) : G → G → G :=
  fun x y => p (f (p.symm x) (p.symm y))

theorem relabel_preserves {G : Type} (f : G → G → G) (p : Equiv.Perm G)
    (r : List (G × G)) (hr : Preserves f r)
    (hp : ∀ a ∈ r, (p a.1, p a.2) ∈ r ∧ (p.symm a.1, p.symm a.2) ∈ r) :
    Preserves (relabel f p) r := by
  intro a ha b hb
  exact (hp _ (hr _ (hp a ha).2 _ (hp b hb).2)).1

theorem relabel_relations (f : Fin 32 → Fin 32 → Fin 32)
    (hf : ∀ j, Preserves f (pairs j)) (i : Fin 5) :
    ∀ j, Preserves (relabel f (perm i)) (pairs j) :=
  fun j => relabel_preserves f (perm i) (pairs j) (hf j) (relation_images i j)

/-- info: 'Magma.WeakCentralSymmetries.inverse' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralSymmetries.inverse
/-- info: 'Magma.WeakCentralSymmetries.fixes_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralSymmetries.fixes_small
/-- info: 'Magma.WeakCentralSymmetries.commutes_rotation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralSymmetries.commutes_rotation
/-- info: 'Magma.WeakCentralSymmetries.relation_images' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 relation_images._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralSymmetries.relation_images
/-- info: 'Magma.WeakCentralSymmetries.relabel_preserves' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralSymmetries.relabel_preserves
/-- info: 'Magma.WeakCentralSymmetries.relabel_relations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 relation_images._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.WeakCentralSymmetries.relabel_relations
end Magma.WeakCentralSymmetries
