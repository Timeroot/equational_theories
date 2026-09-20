import equational_theories.Definability.EndomorphismFamilyCounting
import Mathlib.Algebra.Group.MinimalAxioms

/-! Complete left-translation families restricted by noninvertible endomorphisms. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma.MonoidDihedral8
def A := Fin 8
instance : Fintype A := inferInstanceAs (Fintype (Fin 8))
instance : DecidableEq A := inferInstanceAs (DecidableEq (Fin 8))
instance (n : ℕ) : OfNat A n := inferInstanceAs (OfNat (Fin 8) n)
instance : Inhabited A := ⟨0⟩
def groupData : Array (Array A) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[1, 2, 3, 0, 5, 6, 7, 4], #[2, 3, 0, 1, 6, 7, 4, 5], #[3, 0, 1, 2, 7, 4, 5, 6], #[4, 7, 6, 5, 0, 3, 2, 1], #[5, 4, 7, 6, 1, 0, 3, 2], #[6, 5, 4, 7, 2, 1, 0, 3], #[7, 6, 5, 4, 3, 2, 1, 0]]
def inverseData : Array A := #[0, 3, 2, 1, 4, 5, 6, 7]
instance : Add A := ⟨fun x y => (groupData.getD x.val #[]).getD y.val 0⟩
instance : Zero A := ⟨0⟩
instance : Neg A := ⟨fun x => inverseData.getD x.val 0⟩
instance : AddGroup A := AddGroup.ofLeftAxioms (by native_decide) (by native_decide) (by native_decide)
def mapData : Array (Array A) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 2, 0, 2, 0, 2, 0, 2], #[0, 4, 0, 4, 6, 2, 6, 2], #[0, 0, 0, 0, 0, 0, 0, 0], #[0, 6, 0, 6, 6, 0, 6, 0]]
def mapFunction (i : Fin 5) (x : A) : A := (mapData.getD i.val #[]).getD x.val 0
theorem map_zero : ∀ i, mapFunction i 0 = 0 := by native_decide
theorem map_add : ∀ i x y, mapFunction i (x + y) = mapFunction i x + mapFunction i y := by native_decide
def maps (i : Fin 5) : A →+ A where
  toFun := mapFunction i
  map_zero' := map_zero i
  map_add' := map_add i

def valueData : Array (Array A) := #[#[0, 0, 0, 0, 0, 0, 0, 0], #[0, 2, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 2, 0, 0, 0, 0], #[0, 2, 0, 2, 0, 0, 0, 0], #[0, 0, 0, 0, 0, 2, 0, 0], #[0, 2, 0, 0, 0, 2, 0, 0], #[0, 0, 0, 2, 0, 2, 0, 0], #[0, 2, 0, 2, 0, 2, 0, 0], #[0, 4, 0, 4, 6, 0, 6, 0], #[0, 6, 0, 4, 6, 0, 6, 0], #[0, 4, 0, 6, 6, 0, 6, 0], #[0, 6, 0, 6, 6, 0, 6, 0], #[0, 4, 0, 4, 6, 2, 6, 0], #[0, 6, 0, 4, 6, 2, 6, 0], #[0, 4, 0, 6, 6, 2, 6, 0], #[0, 6, 0, 6, 6, 2, 6, 0], #[0, 0, 0, 0, 0, 0, 0, 2], #[0, 2, 0, 0, 0, 0, 0, 2], #[0, 0, 0, 2, 0, 0, 0, 2], #[0, 2, 0, 2, 0, 0, 0, 2], #[0, 0, 0, 0, 0, 2, 0, 2], #[0, 2, 0, 0, 0, 2, 0, 2], #[0, 0, 0, 2, 0, 2, 0, 2], #[0, 2, 0, 2, 0, 2, 0, 2], #[0, 4, 0, 4, 6, 0, 6, 2], #[0, 6, 0, 4, 6, 0, 6, 2], #[0, 4, 0, 6, 6, 0, 6, 2], #[0, 6, 0, 6, 6, 0, 6, 2], #[0, 4, 0, 4, 6, 2, 6, 2], #[0, 6, 0, 4, 6, 2, 6, 2], #[0, 4, 0, 6, 6, 2, 6, 2], #[0, 6, 0, 6, 6, 2, 6, 2], #[0, 5, 2, 5, 2, 5, 0, 5], #[0, 7, 2, 5, 2, 5, 0, 5], #[0, 5, 2, 7, 2, 5, 0, 5], #[0, 7, 2, 7, 2, 5, 0, 5], #[0, 5, 2, 5, 2, 7, 0, 5], #[0, 7, 2, 5, 2, 7, 0, 5], #[0, 5, 2, 7, 2, 7, 0, 5], #[0, 7, 2, 7, 2, 7, 0, 5], #[0, 1, 2, 1, 4, 5, 6, 5], #[0, 3, 2, 1, 4, 5, 6, 5], #[0, 1, 2, 3, 4, 5, 6, 5], #[0, 3, 2, 3, 4, 5, 6, 5], #[0, 1, 2, 1, 4, 7, 6, 5], #[0, 3, 2, 1, 4, 7, 6, 5], #[0, 1, 2, 3, 4, 7, 6, 5], #[0, 3, 2, 3, 4, 7, 6, 5], #[0, 5, 2, 5, 2, 5, 0, 7], #[0, 7, 2, 5, 2, 5, 0, 7], #[0, 5, 2, 7, 2, 5, 0, 7], #[0, 7, 2, 7, 2, 5, 0, 7], #[0, 5, 2, 5, 2, 7, 0, 7], #[0, 7, 2, 5, 2, 7, 0, 7], #[0, 5, 2, 7, 2, 7, 0, 7], #[0, 7, 2, 7, 2, 7, 0, 7], #[0, 1, 2, 1, 4, 5, 6, 7], #[0, 3, 2, 1, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 3, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 1, 4, 7, 6, 7], #[0, 3, 2, 1, 4, 7, 6, 7], #[0, 1, 2, 3, 4, 7, 6, 7], #[0, 3, 2, 3, 4, 7, 6, 7]]
def values (i : Fin 64) (x : A) : A := (valueData.getD i.val #[]).getD x.val 0
def coordinateData : Array A := #[1, 3, 5, 7]
def coordinate (i : Fin 4) : A := coordinateData.getD i.val 0
def transportData : Array (Fin 4 × Fin 5) := #[(0, 3), (0, 0), (0, 1), (1, 0), (0, 2), (2, 0), (0, 4), (3, 0)]
def transport (x : A) := transportData.getD x.val (0, 0)
def row (p : Fin 4 → A) (x : A) : A := maps (transport x).2 (p (transport x).1)
def key (f : A → A) : ℕ := (Finset.univ : Finset (Fin 8)).sum (fun x => (f x).val * 8 ^ x.val)
def keyData : Array ℕ := #[0, 16, 1024, 1040, 65536, 65552, 66560, 66576, 1599520, 1599536, 1600544, 1600560, 1665056, 1665072, 1666080, 1666096, 4194304, 4194320, 4195328, 4195344, 4259840, 4259856, 4260864, 4260880, 5793824, 5793840, 5794848, 5794864, 5859360, 5859376, 5860384, 5860400, 10660520, 10660536, 10661544, 10661560, 10726056, 10726072, 10727080, 10727096, 12239496, 12239512, 12240520, 12240536, 12305032, 12305048, 12306056, 12306072, 14854824, 14854840, 14855848, 14855864, 14920360, 14920376, 14921384, 14921400, 16433800, 16433816, 16434824, 16434840, 16499336, 16499352, 16500360, 16500376]
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
def recover (f : A → A) : Fin 64 := ⟨findKey (key f) 0 64 8 % 64, Nat.mod_lt _ (by decide)⟩
def cover (p : Fin 4 → A) : Fin 64 := recover (row p)
theorem transport_correct : ∀ x, maps (transport x).2 (coordinate (transport x).1) = x := by native_decide
theorem cover_correct : ∀ p : Fin 4 → A,
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
@[implicit_reducible] def model (p : Fin 64) : Magma A := Magma.EndomorphismFamily.fam values p
theorem translations (p : Fin 64) (a : A) : (model p).IsEndo (Equiv.addLeft a) :=
  Magma.EndomorphismFamily.family_generators maps values values_commute p (.inl a)
theorem move_zero : ∀ a : A, Equiv.addLeft a 0 = a := by intro a; exact add_zero a

private def law1055 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Leaf 0))) (.Leaf 0)))⟩
private theorem count1055 : Fintype.card {p : Fin 64 // PointTest (0 : A) (model p) law1055} = 47 := by native_decide

private def law3458 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count3458 : Fintype.card {p : Fin 64 // PointTest (0 : A) (model p) law3458} = 41 := by native_decide

end Magma.MonoidDihedral8

open Magma.MonoidDihedral8

theorem Equation3458_not_termStructuralFromFin_Equation1055_monoidDihedral8 : ¬ Law3458.TermStructuralFromFin Law1055 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.EndomorphismFamily.gen maps)
    model (Magma.EndomorphismFamily.family_injective values values_injective)
    (Magma.EndomorphismFamily.coverage maps values values_coverage)
    (Magma.EndomorphismFamily.family_generators maps values values_commute)
    (fun p => PointTest (0 : A) (model p) law1055)
    (fun p => PointTest (0 : A) (model p) law3458)
  · intro p hp φ
    exact (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (pointTest_iff_satisfies 0 (model p) Equiv.addLeft (translations p) move_zero _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1055, count3458]
    decide

/-- info: 'Equation3458_not_termStructuralFromFin_Equation1055_monoidDihedral8' depends on axioms: [propext,
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
 count1055._native.native_decide.ax_1_1,
 count3458._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3458_not_termStructuralFromFin_Equation1055_monoidDihedral8

