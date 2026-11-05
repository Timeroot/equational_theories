import equational_theories.Parastrophes.SeededTwistedCycleCompletion
import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All

/-!
# E1695's division image fails closure under submagmas

The seeded completion has vertical shift C and horizontal shift T, and satisfies
D(z,D(y,z))=C(y), D(a,C(a))=T(a), D(a,T(a))=C²(a).
Its left division M has square T(C⁻¹(x)), giving E1695. In the submagma of
nonnegative heights, a zero-height row misses its own index: the required
preimage T(C⁻¹(x)) has height -1.
-/
namespace Parastrophes.Eq1695ImageObstruction
open SeededTwistedCycleCompletion Law FreeMagma
noncomputable section
abbrev Carrier := Point

def op (p : Completed) (x y : Carrier) : Carrier := Classical.choose (p.total x y)
@[implicit_reducible] def division (p : Completed) : Magma Carrier := ⟨op p⟩

theorem op_of_rel (p : Completed) {a b c : Point} (h : p.R a b c) : op p a b=c :=
  p.functional _ _ _ _ (Classical.choose_spec (p.total a b)) h

theorem cross (p : Completed) (y z : Carrier) : op p z (op p y z)=shift 1 y :=
  op_of_rel p (p.rotate _ _ _ (Classical.choose_spec (p.total y z)))

theorem cross_twice (p : Completed) (x y : Carrier) :
    op p (op p x y) (shift 1 x)=shift 1 y := by
  have h := cross p y (op p x y)
  rwa [cross p x y] at h

theorem shift_injective (k : Int) : Function.Injective (shift k) := by
  intro a b h
  have h' := congrArg (shift (-k)) h
  simpa only [shift_shift,add_neg_cancel,shift_zero] using h'

theorem left_injective (p : Completed) (x : Carrier) : Function.Injective (op p x) := by
  intro a b h
  apply shift_injective 1
  rw [← cross_twice p x a,← cross_twice p x b,h]

@[implicit_reducible] def source (p : Completed) : Magma Carrier :=
  ⟨fun x y => op p (shift (-1) y) x⟩

theorem isDivision (p : Completed) : IsDivision .left (division p) (source p) := by
  have hi (x y : Carrier) : op p x (op p (shift (-1) y) x)=y := by
    rw [cross]
    simp
  exact ⟨hi,fun x y => left_injective p x (hi x (op p x y))⟩

theorem quasigroup (p : Completed) : IsQuasigroup (division p) := by
  constructor
  · intro x
    exact ⟨left_injective p x,fun y => ⟨_,(isDivision p).1 x y⟩⟩
  · intro y
    constructor
    · intro a b h
      change op p a y=op p b y at h
      apply shift_injective 1
      rw [← cross p a y,← cross p b y,h]
    · intro x
      refine ⟨op p (shift (-1) y) (shift (-1) x),?_⟩
      simpa using cross_twice p (shift (-1) y) (shift (-1) x)

theorem seed_first (p : Completed) (a : Carrier) : op p a (shift 1 a)=next a :=
  op_of_rel p (p.seeded _ _ _ ⟨a,Or.inl ⟨rfl,rfl,rfl⟩⟩)

theorem seed_second (p : Completed) (a : Carrier) : op p a (next a)=shift 2 a :=
  op_of_rel p (p.seeded _ _ _ ⟨a,Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)))⟩)

theorem square (p : Completed) (x : Carrier) : (source p).op x x=next (shift (-1) x) := by
  simpa only [shift_shift,Int.reduceNeg,Int.reduceAdd,shift_zero] using seed_first p (shift (-1) x)

theorem cube (p : Completed) (x : Carrier) :
    (source p).op ((source p).op x x) x=shift 1 x := by
  rw [square]
  change op p (shift (-1) x) (next (shift (-1) x))=shift 1 x
  rw [seed_second]
  simp

theorem source_law (p : Completed) : @Equation1695 Carrier (source p) := by
  intro x y
  rw [cube]
  change x=op p (shift (-1) (shift 1 y)) ((source p).op y x)
  simp only [shift_shift,Int.reduceNeg,Int.reduceAdd,shift_zero]
  exact ((isDivision p).1 y x).symm

def bounded (x : Carrier) : Prop := 0 ≤ x.2.2

theorem division_bounded (p : Completed) {x y : Carrier} (hx : bounded x) (hy : bounded y) :
    bounded (op p x y) := by
  have hl := p.lower _ _ _ (Classical.choose_spec (p.total x y))
  change 0 ≤ (op p x y).2.2
  change min x.2.2 y.2.2 ≤ (op p x y).2.2 at hl
  unfold bounded at hx hy
  omega

abbrev Subcarrier := {x : Carrier // bounded x}
@[implicit_reducible] def subDivision (p : Completed) : Magma Subcarrier :=
  ⟨fun x y => ⟨op p x.val y.val,division_bounded p x.property y.property⟩⟩
def generator : Subcarrier := ⟨(0,0,0),by change (0 : Int) ≤ 0; omega⟩

theorem sub_not_leftQuasigroup (p : Completed) : ¬ IsSideQuasigroup .left (subDivision p) := by
  intro h
  obtain ⟨⟨y,hy⟩,he⟩ := (h generator).2 generator
  have hv : op p (0,0,0) y=(0,0,0) := congrArg Subtype.val he
  have hi := (isDivision p).2 (0,0,0) y
  change (source p).op (0,0,0) (op p (0,0,0) y)=y at hi
  rw [hv,square] at hi
  rw [← hi] at hy
  change (0 : Int) ≤ -1 at hy
  omega

theorem sub_eval (p : Completed) (t : FreeMagma Nat) (v : Nat → Subcarrier) :
    (@evalInMagma _ _ (subDivision p) v t).val =
      @evalInMagma _ _ (division p) (fun i => (v i).val) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change op p _ _ = _
    rw [ha,hb]
    rfl

/-- The obstruction applies to any source law containing this same model. -/
theorem no_singleEquation_of_source {L : NatMagmaLaw}
    (hsource : @satisfies _ Carrier (source complete) L) :
    ¬ SingleEquation .all L .left := by
  rintro ⟨target,ht⟩
  let p := complete
  have hwhole : @satisfies _ Carrier (division p) target :=
    (ht Carrier (division p) trivial).mpr ⟨source p,hsource,division_symm (isDivision p)⟩
  have hsub : @satisfies _ Subcarrier (subDivision p) target := by
    intro v
    apply Subtype.val_injective
    rw [sub_eval,sub_eval]
    exact hwhole (fun i => (v i).val)
  exact sub_not_leftQuasigroup p
    (characterizes_sideQuasigroup ht Subcarrier (subDivision p) trivial hsub)

theorem no_singleEquation : ¬ SingleEquation .all Law1695 .left :=
  no_singleEquation_of_source ((@Law1695.models_iff _ (source complete)).mpr (source_law complete))

/-- Terms at the zero-height generator stay nonnegative; its M-square does not. -/
theorem inverse_not_term (t : FreeMagma (Fin 2)) :
    (termMagma (division complete) t).op ≠ (source complete).op := by
  have closed (t : FreeMagma (Fin 2)) (v : Fin 2 → Carrier)
      (hv : ∀ i, bounded (v i)) :
      bounded (@evalInMagma _ _ (division complete) v t) := by
    induction t with
    | Leaf i => exact hv i
    | Fork a b ha hb => exact division_bounded complete ha hb
  have hb : bounded ((termMagma (division complete) t).op (0,0,0) (0,0,0)) :=
    closed t _ (fun i => by simp [bounded])
  intro he
  rw [he,square] at hb
  change (0 : Int) ≤ -1 at hb
  omega

end
end Parastrophes.Eq1695ImageObstruction

namespace Parastrophes.Catalogue
/-- A seeded twisted-cycle model has a division submagma whose zero-height
row misses its own index, excluding any equational definition of the image. -/
@[parastrophe_result] theorem left_noSingleEquation1695_all :
    ¬ SingleEquation .all Law1695 .left := Eq1695ImageObstruction.no_singleEquation
end Parastrophes.Catalogue
