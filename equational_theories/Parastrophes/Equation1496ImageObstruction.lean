import equational_theories.Parastrophes.TwistedCycleCompletion
import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All

/-!
# E1496's left-division image is not equational on arbitrary carriers

Complete twisted triples `(a,b,c) -> (b,c,C a)`, where `C` shifts an integer
index upward. Adjoin a right identity `e`, with `e*x=C x` and `x*(C x)=e`.
The result is a quasigroup D satisfying `z*(y*z)=C y`. Its left division M
satisfies E1496. The elements with nonnegative indices, together with e, form
a submagma of D, but its row at e is not surjective. Thus the image is not
closed under submagmas, ruling out even an arbitrary set of identities.
-/
namespace Parastrophes.Eq1496ImageObstruction
open TwistedCycleCompletion Law FreeMagma
noncomputable section
abbrev Carrier := Option Point

def turn (x : Carrier) : Carrier := x.map (shift 1)
def unturn (x : Carrier) : Carrier := x.map (shift (-1))

@[simp] theorem turn_unturn (x : Carrier) : turn (unturn x)=x := by
  cases x <;> simp [turn,unturn]
@[simp] theorem unturn_turn (x : Carrier) : unturn (turn x)=x := by
  cases x <;> simp [turn,unturn]

theorem turn_injective : Function.Injective turn :=
  Function.LeftInverse.injective unturn_turn

def op (p : Completed) : Carrier → Carrier → Carrier
  | none, y => turn y
  | some x, none => some x
  | some x, some y => if h : y=shift 1 x then none else some (Classical.choose (p.total x y h))

@[implicit_reducible] def division (p : Completed) : Magma Carrier := ⟨op p⟩

@[simp] theorem right_unit (p : Completed) (x : Carrier) : op p x none=x := by
  cases x <;> rfl
@[simp] theorem left_unit (p : Completed) (x : Carrier) : op p none x=turn x := rfl

theorem op_of_rel (p : Completed) {a b c : Point} (h : p.R a b c) :
    op p (some a) (some b)=some c := by
  simp only [op,dif_neg (p.avoid _ _ _ h)]
  exact congrArg some (p.functional _ _ _ _ (Classical.choose_spec (p.total _ _ (p.avoid _ _ _ h))) h)

/-- The cyclic rule, including triples involving the right identity. -/
theorem cross (p : Completed) (y z : Carrier) : op p z (op p y z)=turn y := by
  rcases y with _ | y <;> rcases z with _ | z
  · rfl
  · simp [op,turn]
  · simp [right_unit,left_unit]
  · by_cases h : z=shift 1 y
    · simp only [op,dif_pos h]
      exact congrArg some h
    · let c := Classical.choose (p.total y z h)
      have hc : p.R y z c := Classical.choose_spec (p.total y z h)
      rw [op_of_rel p hc,op_of_rel p (p.rotate _ _ _ hc)]
      rfl

theorem cross_twice (p : Completed) (x y : Carrier) :
    op p (op p x y) (turn x)=turn y := by
  have h := cross p y (op p x y)
  rwa [cross p x y] at h

theorem left_injective (p : Completed) (x : Carrier) : Function.Injective (op p x) := by
  intro a b h
  apply turn_injective
  rw [← cross_twice p x a, ← cross_twice p x b, h]

theorem quasigroup (p : Completed) : IsQuasigroup (division p) := by
  constructor
  · intro x
    exact ⟨left_injective p x,fun y => ⟨op p (unturn y) x,
      (cross p (unturn y) x).trans (turn_unturn y)⟩⟩
  · intro y
    constructor
    · intro a b h
      change op p a y=op p b y at h
      apply turn_injective
      rw [← cross p a y,← cross p b y,h]
    · intro x
      exact ⟨op p (unturn y) (unturn x),by
        simpa only [turn_unturn] using cross_twice p (unturn y) (unturn x)⟩

/-- The inverse uses the downward shift; the positive submagma cannot perform it. -/
@[implicit_reducible] def source (p : Completed) : Magma Carrier :=
  ⟨fun x y => op p (unturn y) x⟩

theorem isDivision (p : Completed) : IsDivision .left (division p) (source p) := by
  have hi (x y : Carrier) : op p x (op p (unturn y) x)=y := by
    rw [cross,turn_unturn]
  exact ⟨hi,fun x y => left_injective p x (hi x (op p x y))⟩

theorem square (p : Completed) (x : Carrier) : (source p).op x x=none := by
  apply left_injective p x
  exact ((isDivision p).1 x x).trans (right_unit p x).symm

theorem source_at_unit (p : Completed) (x : Carrier) : (source p).op x none=turn x := rfl

theorem source_law (p : Completed) : @Equation1496 Carrier (source p) := by
  intro x y z
  rw [square,source_at_unit]
  change x=op p (unturn (turn y)) ((source p).op y x)
  rw [unturn_turn]
  exact ((isDivision p).1 y x).symm

/-- The entire nonnegative half of each orbit, and the right identity. -/
def bounded : Carrier → Prop
  | none => True
  | some x => 0 ≤ x.2

theorem division_bounded (p : Completed) {x y : Carrier} (hx : bounded x) (hy : bounded y) :
    bounded (op p x y) := by
  rcases x with _ | x <;> rcases y with _ | y
  · trivial
  · change 0 ≤ y.2+1
    change 0 ≤ y.2 at hy
    omega
  · exact hx
  · simp only [op]
    split_ifs with h
    · trivial
    · change 0 ≤ (Classical.choose (p.total x y h)).2
      have hl := p.lower _ _ _ (Classical.choose_spec (p.total x y h))
      change 0 ≤ x.2 at hx
      change 0 ≤ y.2 at hy
      omega

abbrev Subcarrier := {x : Carrier // bounded x}
@[implicit_reducible] def subDivision (p : Completed) : Magma Subcarrier :=
  ⟨fun x y => ⟨op p x.val y.val,division_bounded p x.property y.property⟩⟩
def unit : Subcarrier := ⟨none,trivial⟩
def generator : Subcarrier := ⟨some (0,0),by change (0 : Int) ≤ 0; omega⟩

theorem sub_not_leftQuasigroup (p : Completed) : ¬ IsSideQuasigroup .left (subDivision p) := by
  intro h
  obtain ⟨⟨y,hy⟩,he⟩ := (h unit).2 generator
  have hv := congrArg Subtype.val he
  change turn y=some (0,0) at hv
  cases y with
  | none => cases hv
  | some y =>
    have hs := congrArg (fun v : Carrier => v.map Prod.snd) hv
    simp only [turn,Option.map_some,shift_snd,Option.some.injEq] at hs
    change 0 ≤ y.2 at hy
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

/-- Any source law containing this model has an image that fails closure
under submagmas, since the same inherited submagma lacks left division. -/
theorem no_singleEquation_of_source {L : NatMagmaLaw}
    (hsource : @satisfies _ Carrier (source complete) L) :
    ¬ SingleEquation .all L .left := by
  rintro ⟨target,ht⟩
  let p := complete
  have hwhole : @satisfies _ Carrier (division p) target := by
    apply (ht Carrier (division p) trivial).mpr
    exact ⟨source p,hsource,
      division_symm (isDivision p)⟩
  have hsub : @satisfies _ Subcarrier (subDivision p) target := by
    intro v
    apply Subtype.val_injective
    rw [sub_eval,sub_eval]
    exact hwhole (fun i => (v i).val)
  exact sub_not_leftQuasigroup p
    (characterizes_sideQuasigroup ht Subcarrier (subDivision p) trivial hsub)

theorem no_singleEquation : ¬ SingleEquation .all Law1496 .left :=
  no_singleEquation_of_source ((@Law1496.models_iff _ (source complete)).mpr
    (source_law complete))

theorem no_singleEquation1492 : ¬ SingleEquation .all Law1492 .left :=
  no_singleEquation_of_source ((@Law1492.models_iff _ (source complete)).mpr
    (fun x y => source_law complete x y y))

/-- Even on this one infinite model, no multiplication term in the division
operation recovers its inverse. The term stays inside the positive submagma. -/
theorem inverse_not_term (t : FreeMagma (Fin 2)) :
    (termMagma (division complete) t).op ≠ (source complete).op := by
  have closed (t : FreeMagma (Fin 2)) (v : Fin 2 → Carrier)
      (hv : ∀ i, bounded (v i)) :
      bounded (@evalInMagma _ _ (division complete) v t) := by
    induction t with
    | Leaf i => exact hv i
    | Fork a b ha hb => exact division_bounded complete ha hb
  intro he
  have hb : bounded ((termMagma (division complete) t).op none (some (0,0))) :=
    closed t _ (fun i => by split_ifs <;> first | trivial | change (0 : Int) ≤ 0; omega)
  rw [he] at hb
  change (0 : Int) ≤ -1 at hb
  omega

end
end Parastrophes.Eq1496ImageObstruction

namespace Parastrophes.Catalogue
/-- A quasigroup constructed from shifted three-cycles has a division
submagma whose identity row misses index zero. Thus the arbitrary-carrier
left image of E1496 is not closed under submagmas. -/
@[parastrophe_result] theorem left_noSingleEquation1496_all :
    ¬ SingleEquation .all Law1496 .left := Eq1496ImageObstruction.no_singleEquation

/-- The same E1496 source also satisfies E1492. Its division has a submagma
lacking left division, ruling out every equational characterization of this image. -/
@[parastrophe_result] theorem left_noSingleEquation1492_all :
    ¬ SingleEquation .all Law1492 .left := Eq1496ImageObstruction.no_singleEquation1492
end Parastrophes.Catalogue
