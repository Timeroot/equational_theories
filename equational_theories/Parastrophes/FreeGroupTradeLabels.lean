import equational_theories.Parastrophes.FreeGroupTradeBlocks
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing

/-!
# Fresh injective labels for the group trades

Each pair of free words receives a different generator index, larger than
all indices in the pair. Exponent sums at the larger fresh index distinguish
new orbit points belonging to different trades. This works for an infinite
family; a finite collection can later be represented in a finite group.
-/
namespace Parastrophes.FreeGroupTradeLabels
open FreeGroupWordCones GroupTriangleTrades

private instance : Countable Word := FreeGroup.toWord_injective.countable

noncomputable def encoding (x : Word × Word) : Nat :=
  @Encodable.encode _ (Encodable.ofCountable _) x

theorem encoding_injective : Function.Injective encoding :=
  @Encodable.encode_injective _ (Encodable.ofCountable _)

def support (x : Word × Word) : Finset Nat :=
  (x.1.toWord.map Prod.fst).toFinset ∪ (x.2.toWord.map Prod.fst).toFinset

def bound (x : Word × Word) := (support x).sup id

noncomputable def label (x : Word × Word) := Nat.pair (encoding x) (bound x) + 2

theorem label_pos (x : Word × Word) : 0 < label x := by unfold label; omega

theorem label_injective : Function.Injective label := by
  intro x y he
  have hp : Nat.pair (encoding x) (bound x) = Nat.pair (encoding y) (bound y) := by
    unfold label at he
    omega
  exact encoding_injective (Nat.pair_eq_pair.mp hp).1

theorem fresh_of_label_le (x : Word × Word) {k : Nat} (hk : label x ≤ k) :
    Fresh k x.1 ∧ Fresh k x.2 := by
  have hb : bound x < k := by
    have h := Nat.right_le_pair (encoding x) (bound x)
    unfold label at hk
    omega
  have hf (e : Nat × Bool) (he : e ∈ x.1.toWord ∨ e ∈ x.2.toWord) : e.1 ≠ k := by
    have hm : e.1 ∈ support x := by
      apply Finset.mem_union.mpr
      rcases he with he | he
      · exact Or.inl (List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩))
      · exact Or.inr (List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩))
    have hl : e.1 ≤ bound x := Finset.le_sup (f := id) hm
    omega
  exact ⟨fun e he => hf e (Or.inl he), fun e he => hf e (Or.inr he)⟩

def weight (k : Nat) (x : Word) : Int :=
  (FreeGroup.lift (fun i => Multiplicative.ofAdd (if i=k then (1 : Int) else 0)) x).toAdd

@[simp] theorem weight_mul (k) (x y : Word) : weight k (x*y) = weight k x + weight k y := by
  simp [weight,map_mul]

@[simp] theorem weight_inv (k) (x : Word) : weight k x⁻¹ = -weight k x := by
  simp [weight,map_inv]

@[simp] theorem weight_of (k i) : weight k (FreeGroup.of i) = if i=k then 1 else 0 := by
  simp [weight]

theorem weight_fresh {k} {x : Word} (hf : Fresh k x) : weight k x = 0 := by
  let f := fun i => Multiplicative.ofAdd (if i=k then (1 : Int) else 0)
  have he : FreeGroup.lift f x = 1 := by
    rw [← FreeGroup.mk_toWord (x := x),FreeGroup.lift_mk]
    apply List.prod_eq_one
    intro a ha
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
    have hn := hf e he
    simp [f,hn]
  exact congrArg Multiplicative.toAdd he

/-- Exponent sums of the six new points. They are distinct and nonzero. -/
def mark (i j : Fin 3) : Int × Int :=
  if i=0 then (0,0) else if i=1 then
    if j=0 then (1,1) else if j=1 then (1,-2) else (-2,1)
  else if j=0 then (-1,-1) else if j=1 then (-1,2) else (2,-1)

theorem mark_nonzero {i j : Fin 3} (hi : i ≠ 0) : mark i j ≠ (0,0) := by
  revert i j
  decide

theorem mark_injective {i j k l : Fin 3} (hi : i ≠ 0) (hk : k ≠ 0)
    (he : mark i j = mark k l) : i=k ∧ j=l := by
  revert i j k l
  decide

theorem point_weight (x : Word × Word) (i j : Fin 3) :
    (weight (label x) (orbit (row x (FreeGroup.of (label x)) i) j).1,
      weight (label x) (orbit (row x (FreeGroup.of (label x)) i) j).2) = mark i j := by
  have hx := fresh_of_label_le x le_rfl
  have ha := weight_fresh hx.1
  have hb := weight_fresh hx.2
  fin_cases i <;> fin_cases j <;> simp [orbit,row,rotate,mark,ha,hb]

theorem point_weight_above (x : Word × Word) {k : Nat} (hk : label x < k) (i j : Fin 3) :
    (weight k (orbit (row x (FreeGroup.of (label x)) i) j).1,
      weight k (orbit (row x (FreeGroup.of (label x)) i) j).2) = (0,0) := by
  have hx := fresh_of_label_le x hk.le
  have ha := weight_fresh hx.1
  have hb := weight_fresh hx.2
  have he : label x ≠ k := Nat.ne_of_lt hk
  fin_cases i <;> fin_cases j <;> simp [orbit,row,rotate,ha,hb,he]

end Parastrophes.FreeGroupTradeLabels
