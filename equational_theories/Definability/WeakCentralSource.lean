import equational_theories.Definability.GenerationOrder
import equational_theories.Equations.All

/-! Verified source data and necessary preservation properties for the
E1485 to E1483 term-recovery search. This file contains no exclusion theorem. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Magma.WeakCentralSource
open Magma.GenerationOrder

def rot (x : Nat) : Nat := (2*x)%32 + x/16
def back (x : Nat) : Nat := x/2 + 16*(x%2)

@[implicit_reducible] def source : Magma (Fin 32) where
  op x y := ⟨(31 ^^^ (rot x.val &&& back y.val))%32, Nat.mod_lt _ (by decide)⟩

def rotation (x : Fin 32) : Fin 32 := ⟨rot x.val % 32, Nat.mod_lt _ (by decide)⟩

theorem source_law : @Equation1485 (Fin 32) source := by decide

theorem source_rotation : ∀ x y, source.op (rotation x) (rotation y) = rotation (source.op x y) := by decide

theorem source_idempotents : ∀ x : Fin 32, source.op x x = x ↔ x = 11 ∨ x = 13 ∨ x = 21 ∨ x = 22 ∨ x = 26 := by decide

abbrev pairSeeds : Set (Fin 32) := {11, 21}
private def pairRank : Fin 32 → Nat := ![31, 23, 25, 18, 27, 9, 26, 11, 29, 4, 10, 0, 21, 2, 20, 8, 30, 22, 12, 24, 7, 1, 17, 15, 28, 5, 19, 13, 16, 6, 3, 14]
private def pairLeft : Fin 32 → Fin 32 := ![31, 15, 30, 30, 29, 13, 30, 30, 27, 11, 30, 0, 25, 11, 30, 13, 31, 15, 30, 7, 21, 0, 21, 21, 27, 11, 30, 11, 21, 21, 21, 11]
private def pairRight : Fin 32 → Fin 32 := ![31, 29, 27, 25, 31, 21, 23, 21, 15, 13, 11, 0, 15, 21, 7, 11, 30, 30, 30, 25, 30, 0, 18, 25, 30, 30, 10, 10, 15, 13, 11, 18]

def pairOrder : Witness source.op pairSeeds where
  before x y := pairRank x < pairRank y
  irrefl x := Nat.lt_irrefl _
  trans _ _ _ := Nat.lt_trans
  total := by decide
  seeds_first := by decide
  parents z hz := by
    refine ⟨pairLeft z, pairRight z, ?_⟩
    have hh : ∀ z ∉ pairSeeds,
        source.op (pairLeft z) (pairRight z) = z ∧
        pairRank (pairLeft z) < pairRank z ∧
        pairRank (pairRight z) < pairRank z := by decide
    exact hh z hz

theorem pair_generates (x : Fin 32) : Generated source.op pairSeeds x :=
  pairOrder.generated x

abbrev oneSeeds : Set (Fin 32) := {1}
private def oneRank : Fin 32 → Nat := ![4, 0, 17, 18, 6, 7, 20, 16, 5, 9, 19, 13, 8, 11, 21, 3, 22, 23, 25, 26, 28, 15, 30, 14, 24, 12, 27, 10, 29, 2, 31, 1]
private def oneLeft : Fin 32 → Fin 32 := ![31, 0, 31, 31, 29, 29, 29, 12, 31, 15, 31, 31, 29, 31, 29, 31, 23, 23, 23, 23, 23, 5, 21, 4, 23, 31, 23, 31, 23, 1, 21, 1]
private def oneRight : Fin 32 → Fin 32 := ![31, 0, 27, 25, 31, 29, 27, 31, 15, 15, 11, 9, 15, 5, 11, 1, 31, 29, 27, 25, 23, 31, 27, 31, 15, 12, 11, 8, 7, 31, 11, 1]

def oneOrder : Witness source.op oneSeeds where
  before x y := oneRank x < oneRank y
  irrefl x := Nat.lt_irrefl _
  trans _ _ _ := Nat.lt_trans
  total := by decide
  seeds_first := by decide
  parents z hz := by
    refine ⟨oneLeft z, oneRight z, ?_⟩
    have hh : ∀ z ∉ oneSeeds,
        source.op (oneLeft z) (oneRight z) = z ∧
        oneRank (oneLeft z) < oneRank z ∧
        oneRank (oneRight z) < oneRank z := by decide
    exact hh z hz

theorem one_generates (x : Fin 32) : Generated source.op oneSeeds x :=
  oneOrder.generated x

abbrev threeSeeds : Set (Fin 32) := {3}
private def threeRank : Fin 32 → Nat := ![4, 20, 10, 0, 25, 27, 22, 18, 12, 21, 16, 15, 7, 26, 3, 8, 24, 13, 31, 11, 30, 29, 28, 19, 6, 2, 23, 5, 9, 14, 17, 1]
private def threeLeft : Fin 32 → Fin 32 := ![31, 15, 31, 0, 31, 15, 28, 12, 31, 15, 27, 14, 25, 25, 31, 25, 31, 31, 30, 31, 29, 29, 28, 12, 31, 3, 31, 3, 25, 25, 24, 3]
private def threeRight : Fin 32 → Fin 32 := ![31, 31, 27, 0, 23, 23, 31, 31, 15, 15, 27, 15, 31, 29, 3, 25, 30, 28, 30, 24, 30, 28, 30, 24, 14, 31, 10, 25, 14, 12, 14, 3]

def threeOrder : Witness source.op threeSeeds where
  before x y := threeRank x < threeRank y
  irrefl x := Nat.lt_irrefl _
  trans _ _ _ := Nat.lt_trans
  total := by decide
  seeds_first := by decide
  parents z hz := by
    refine ⟨threeLeft z, threeRight z, ?_⟩
    have hh : ∀ z ∉ threeSeeds,
        source.op (threeLeft z) (threeRight z) = z ∧
        threeRank (threeLeft z) < threeRank z ∧
        threeRank (threeRight z) < threeRank z := by decide
    exact hh z hz

theorem three_generates (x : Fin 32) : Generated source.op threeSeeds x :=
  threeOrder.generated x

abbrev sevenSeeds : Set (Fin 32) := {7}
private def sevenRank : Fin 32 → Nat := ![22, 19, 30, 20, 13, 4, 18, 0, 23, 21, 31, 27, 3, 7, 17, 10, 15, 2, 28, 12, 14, 11, 26, 5, 16, 6, 29, 24, 8, 1, 25, 9]
private def sevenLeft : Fin 32 → Fin 32 := ![31, 31, 31, 31, 29, 29, 28, 0, 31, 31, 31, 31, 29, 29, 28, 12, 23, 7, 23, 7, 23, 5, 23, 7, 23, 7, 23, 7, 17, 7, 17, 17]
private def sevenRight : Fin 32 → Fin 32 := ![31, 29, 27, 25, 23, 29, 23, 0, 15, 13, 11, 9, 7, 5, 7, 7, 31, 29, 27, 25, 23, 29, 19, 17, 15, 12, 11, 9, 7, 7, 19, 17]

def sevenOrder : Witness source.op sevenSeeds where
  before x y := sevenRank x < sevenRank y
  irrefl x := Nat.lt_irrefl _
  trans _ _ _ := Nat.lt_trans
  total := by decide
  seeds_first := by decide
  parents z hz := by
    refine ⟨sevenLeft z, sevenRight z, ?_⟩
    have hh : ∀ z ∉ sevenSeeds,
        source.op (sevenLeft z) (sevenRight z) = z ∧
        sevenRank (sevenLeft z) < sevenRank z ∧
        sevenRank (sevenRight z) < sevenRank z := by decide
    exact hh z hz

theorem seven_generates (x : Fin 32) : Generated source.op sevenSeeds x :=
  sevenOrder.generated x

theorem rotation_of_termDefinable {N : Magma (Fin 32)}
    (h : @Set.TermDefinable _ ∅ MagmaLanguage source.FOStructure _ N.FinArityOp) :
    ∀ x y, N.op (rotation x) (rotation y) = rotation (N.op x y) := by
  have hP : source.IsCloneInvariant (fun f => ∀ x y, f (rotation x) (rotation y) = rotation (f x y)) :=
    { fst := fun _ _ => rfl
      snd := fun _ _ => rfl
      comp := by
        intro f g hf hg x y
        dsimp only
        rw [hf, hg, source_rotation] }
  exact hP.of_termDefinable h

theorem idempotent_of_termDefinable {G : Type} {M N : Magma G} (x : G)
    (h : @Set.TermDefinable _ ∅ MagmaLanguage M.FOStructure _ N.FinArityOp)
    (hx : M.op x x = x) : N.op x x = x := by
  have hP : M.IsCloneInvariant (fun f => f x x = x) :=
    { fst := rfl
      snd := rfl
      comp := by
        intro f g hf hg
        dsimp only
        rw [hf, hg, hx] }
  exact hP.of_termDefinable h

theorem recovered_idempotents {N : Magma (Fin 32)}
    (hf : @Set.TermDefinable _ ∅ MagmaLanguage source.FOStructure _ N.FinArityOp)
    (hr : @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ source.FinArityOp)
    (x : Fin 32) : N.op x x = x ↔ x = 11 ∨ x = 13 ∨ x = 21 ∨ x = 22 ∨ x = 26 := by
  rw [← source_idempotents x]
  exact ⟨idempotent_of_termDefinable x hr, idempotent_of_termDefinable x hf⟩

noncomputable def recovered_pair_order {N : Magma (Fin 32)}
    (hr : @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ source.FinArityOp) :
    Witness N.op pairSeeds := finiteWitness_of_recovery pairSeeds hr pair_generates

/-- info: 'Magma.WeakCentralSource.source_law' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms source_law
/-- info: 'Magma.WeakCentralSource.source_rotation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms source_rotation
/-- info: 'Magma.WeakCentralSource.source_idempotents' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms source_idempotents
/-- info: 'Magma.WeakCentralSource.pair_generates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pair_generates
/-- info: 'Magma.WeakCentralSource.one_generates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_generates
/-- info: 'Magma.WeakCentralSource.three_generates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms three_generates
/-- info: 'Magma.WeakCentralSource.seven_generates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seven_generates
/-- info: 'Magma.WeakCentralSource.rotation_of_termDefinable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rotation_of_termDefinable
/-- info: 'Magma.WeakCentralSource.recovered_idempotents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recovered_idempotents
/-- info: 'Magma.WeakCentralSource.recovered_pair_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recovered_pair_order
end Magma.WeakCentralSource
