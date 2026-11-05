import equational_theories.Parastrophes.SeededTwistedCycleCompletion
import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All

/-!
# E880's left-division image is not equational

A twisted-cycle quasigroup H with H(x,x)=C²x gives an E880 magma
M(x,y)=C⁻¹H(x,y). Its left division is H with its arguments exchanged.
Additional prescribed products put the inverse of a positive pair at height -1.
-/
namespace Parastrophes.Eq880ImageObstruction
open SeededTwistedCycleCompletion Law FreeMagma
noncomputable section
def Seed (x y z : Point) : Prop := ∃ a,
  (x=a ∧ y=shift 1 a ∧ z=next a) ∨
  (x=shift 1 a ∧ y=next a ∧ z=shift 1 a) ∨
  (x=next a ∧ y=shift 1 a ∧ z=shift 2 a) ∨
  (x=a ∧ y=a ∧ z=shift 2 a) ∨
  (x=a ∧ y=shift 2 a ∧ z=shift 1 a) ∨
  (x=shift 2 a ∧ y=shift 1 a ∧ z=shift 1 a)

theorem seed_functional {x y z w : Point} (h : Seed x y z) (h' : Seed x y w) : z=w := by
  obtain ⟨a,h⟩ := h
  obtain ⟨b,h'⟩ := h'
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals
    rcases h' with ⟨hx,hy,rfl⟩ | ⟨hx,hy,rfl⟩ | ⟨hx,hy,rfl⟩ |
      ⟨hx,hy,rfl⟩ | ⟨hx,hy,rfl⟩ | ⟨hx,hy,rfl⟩
    all_goals
      have hx1 := congrArg Prod.fst hx
      have hx2 := congrArg (fun p : Point => p.2.1) hx
      have hx3 := congrArg (fun p : Point => p.2.2) hx
      have hy2 := congrArg (fun p : Point => p.2.1) hy
      have hy3 := congrArg (fun p : Point => p.2.2) hy
      apply Prod.ext
      · simpa only [shift,next] using hx1
      · apply Prod.ext <;> simp only [shift,next] at * <;> omega

theorem seed_rotate {x y z : Point} (h : Seed x y z) : Seed y z (shift 1 x) := by
  obtain ⟨a,h⟩ := h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact ⟨x,Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)⟩
  · exact ⟨a,Or.inr (Or.inr (Or.inl ⟨rfl,rfl,by simp⟩))⟩
  · exact ⟨shift 1 a,Or.inl ⟨rfl,by simp,by simp⟩⟩
  · exact ⟨y,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩))))⟩
  · exact ⟨x,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl,rfl⟩))))⟩
  · exact ⟨shift 1 a,Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,by simp,by simp⟩)))⟩

theorem seed_translate {x y z : Point} (h : Seed x y z) (k : Int) :
    Seed (shift k x) (shift k y) (shift k z) := by
  obtain ⟨a,h⟩ := h
  refine ⟨shift k a,?_⟩
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals simp [shift,next,add_right_comm]

theorem seed_same_block {x y z : Point} (h : Seed x y z) : x.1=y.1 := by
  obtain ⟨a,h⟩ := h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals rfl

theorem seed_lower {x y z : Point} (h : Seed x y z) : min x.2.2 y.2.2 ≤ z.2.2 := by
  obtain ⟨a,h⟩ := h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals simp only [shift,next]; omega

def seed880 : SeedData :=
  ⟨Seed,fun _ _ _ _ => seed_functional,fun _ _ _ => seed_rotate,
    fun _ _ _ => seed_translate,fun _ _ _ => seed_same_block,fun _ _ _ => seed_lower⟩

abbrev Carrier := Point
abbrev Completion := Completed seed880

def op (p : Completion) (x y : Carrier) : Carrier := Classical.choose (p.total x y)

theorem op_of_rel (p : Completion) {a b c : Point} (h : p.R a b c) : op p a b=c :=
  p.functional _ _ _ _ (Classical.choose_spec (p.total a b)) h

theorem cross (p : Completion) (y z : Carrier) : op p z (op p y z)=shift 1 y :=
  op_of_rel p (p.rotate _ _ _ (Classical.choose_spec (p.total y z)))

theorem cross_twice (p : Completion) (x y : Carrier) :
    op p (op p x y) (shift 1 x)=shift 1 y := by
  have h := cross p y (op p x y)
  rwa [cross p x y] at h

theorem shift_injective (k : Int) : Function.Injective (shift k) := by
  intro a b h
  have h' := congrArg (shift (-k)) h
  simpa only [shift_shift,add_neg_cancel,shift_zero] using h'

theorem left_injective (p : Completion) (x : Carrier) : Function.Injective (op p x) := by
  intro a b h
  apply shift_injective 1
  rw [← cross_twice p x a,← cross_twice p x b,h]

@[implicit_reducible] def source (p : Completion) : Magma Carrier :=
  ⟨fun x y => shift (-1) (op p x y)⟩
@[implicit_reducible] def division (p : Completion) : Magma Carrier := ⟨fun x y => op p y x⟩

theorem isDivision (p : Completion) : IsDivision .left (source p) (division p) := by
  constructor
  · intro x y
    change shift (-1) (op p x (op p y x))=y
    rw [cross]
    simp
  · intro x y
    apply left_injective p x
    change op p x (op p (shift (-1) (op p x y)) x)=op p x y
    rw [cross]
    simp

theorem seed_first (p : Completion) (a : Carrier) : op p a (shift 1 a)=next a :=
  op_of_rel p (p.seeded _ _ _ ⟨a,Or.inl ⟨rfl,rfl,rfl⟩⟩)

theorem diagonal (p : Completion) (a : Carrier) : op p a a=shift 2 a :=
  op_of_rel p (p.seeded _ _ _ ⟨a,Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)))⟩)

theorem square (p : Completion) (x : Carrier) : (source p).op x x=shift 1 x := by
  change shift (-1) (op p x x)=shift 1 x
  rw [diagonal]
  simp

theorem source_law (p : Completion) : @Equation880 Carrier (source p) := by
  intro x y
  rw [square]
  change x=shift (-1) (op p y (shift 1 (shift (-1) (op p x y))))
  simp only [shift_shift,Int.reduceNeg,Int.reduceAdd,shift_zero]
  rw [cross]
  simp

def bounded (x : Carrier) : Prop := 0 ≤ x.2.2

theorem division_bounded (p : Completion) {x y : Carrier} (hx : bounded x) (hy : bounded y) :
    bounded ((division p).op x y) := by
  have hl := p.lower _ _ _ (Classical.choose_spec (p.total y x))
  change 0 ≤ (op p y x).2.2
  change min y.2.2 x.2.2 ≤ (op p y x).2.2 at hl
  unfold bounded at hx hy
  omega

abbrev Subcarrier := {x : Carrier // bounded x}
@[implicit_reducible] def subDivision (p : Completion) : Magma Subcarrier :=
  ⟨fun x y => ⟨(division p).op x.val y.val,division_bounded p x.property y.property⟩⟩
def generator : Subcarrier := ⟨(0,0,0),by change (0 : Int) ≤ 0; omega⟩
def target : Subcarrier := ⟨(0,0,1),by change (0 : Int) ≤ 1; omega⟩

theorem sub_not_leftQuasigroup (p : Completion) : ¬ IsSideQuasigroup .left (subDivision p) := by
  intro h
  obtain ⟨⟨y,hy⟩,he⟩ := (h generator).2 target
  have hv : (division p).op (0,0,0) y=(0,0,1) := congrArg Subtype.val he
  have hi := (isDivision p).1 (0,0,0) y
  rw [hv] at hi
  change shift (-1) (op p (0,0,0) (shift 1 (0,0,0)))=y at hi
  rw [seed_first] at hi
  rw [← hi] at hy
  change (0 : Int) ≤ -1 at hy
  omega

theorem sub_eval (p : Completion) (t : FreeMagma Nat) (v : Nat → Subcarrier) :
    (@evalInMagma _ _ (subDivision p) v t).val =
      @evalInMagma _ _ (division p) (fun i => (v i).val) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change op p _ _ = _
    rw [ha,hb]
    rfl

theorem no_singleEquation : ¬ SingleEquation .all Law880 .left := by
  rintro ⟨L,ht⟩
  let p := complete seed880
  have hwhole : @satisfies _ Carrier (division p) L :=
    (ht Carrier (division p) trivial).mpr
      ⟨source p,(@Law880.models_iff _ (source p)).mpr (source_law p),isDivision p⟩
  have hsub : @satisfies _ Subcarrier (subDivision p) L := by
    intro v
    apply Subtype.val_injective
    rw [sub_eval,sub_eval]
    exact hwhole (fun i => (v i).val)
  exact sub_not_leftQuasigroup p
    (characterizes_sideQuasigroup ht Subcarrier (subDivision p) trivial hsub)

end
end Parastrophes.Eq880ImageObstruction

namespace Parastrophes.Catalogue
/-- A seeded twisted-cycle model gives an actual E880 division with a
submagma lacking left division. This excludes every equational definition. -/
@[parastrophe_result] theorem left_noSingleEquation880_all :
    ¬ SingleEquation .all Law880 .left := Eq880ImageObstruction.no_singleEquation
end Parastrophes.Catalogue
