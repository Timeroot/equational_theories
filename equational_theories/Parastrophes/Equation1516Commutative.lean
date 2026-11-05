import equational_theories.Parastrophes.Equation1516Image

/-!
# The E1516 image criterion in commutative magmas

The unrestricted converse to `Common + Short` is false; see the 38-element
model in `Equation1516CommonCounterexample`. Within the commutative class
the image has an exact description on arbitrary carriers:
idempotence and E75, saying every row has cube equal to the identity.

Every row cube is the same map c. Consequently c commutes with every row.
Moving c through Short gives `c²(u(x))=x`, where `u(x)=x*(x*x)`. Also
`u(c(x))=c³(u(x))=c(x)`. Surjectivity of c now gives u=id and c²=id.
Applying these relations to the diagonal gives c=id and idempotence.
Conversely, square each row to recover the source multiplication explicitly.
The forward direction for actual images uses row cancellation to obtain the
source square inverse; it needs no finiteness either.

No commutativity of the source multiplication is assumed: it is the proposed
division operation that is commutative. No unconditional characterization
attribute belongs on this restricted result.
-/
namespace Parastrophes.Eq1516Image
open Law

section
variable {A : Type} (D : Magma A)
    (comm : ∀ x y, D.op x y = D.op y x) (hc : Common D)
include comm hc

/-- In the commutative case, the common map is the cube of every row. -/
theorem turn_eq_row_cube (x y : A) :
    turn D x = D.op y (D.op y (D.op y x)) := by
  rw [← hc x y]
  unfold cross
  rw [comm x y]

/-- A row commutes with its cube, which here is independent of the row. -/
theorem turn_commutes_row (x y : A) :
    turn D (D.op x y) = D.op x (turn D y) := by
  rw [turn_eq_row_cube D comm hc (D.op x y) x,
    turn_eq_row_cube D comm hc y x]

/-- The short identity supplies an explicit right inverse to c². This is
a surjectivity argument on arbitrary carriers, before using finiteness. -/
theorem turn_twice_right_inverse (hs : Short D) (x : A) :
    turn D (turn D (D.op x (D.op x x))) = x := by
  have move_left (a b : A) : turn D (D.op a b) = D.op (turn D a) b := by
    rw [comm a b, turn_commutes_row D comm hc, comm b]
  calc
    turn D (turn D (D.op x (D.op x x))) =
        D.op (turn D x) (turn D (D.op x x)) := by
      rw [turn_commutes_row D comm hc, move_left]
    _ = D.op (turn D x) (D.op x (turn D x)) := by
      rw [turn_commutes_row D comm hc]
    _ = x := by simpa only [hc] using hs x x x

theorem turn_surjective_of_commutative (hs : Short D) :
    Function.Surjective (turn D) := fun x =>
  ⟨turn D (D.op x (D.op x x)), turn_twice_right_inverse D comm hc hs x⟩

theorem rows_surjective_of_commutative (hs : Short D) :
    ∀ y, Function.Surjective (D.op y) := by
  intro y x
  obtain ⟨z, rfl⟩ := turn_surjective_of_commutative D comm hc hs x
  exact ⟨D.op y (D.op z y), hc z y⟩

/-- The common map in fact has to be the identity. The argument is valid
on infinite carriers too; no finite permutation orders are used. -/
theorem turn_eq_self_of_commutative (hs : Short D) (x : A) : turn D x = x := by
  let u := fun x => D.op x (D.op x x)
  have move_left (a b : A) : turn D (D.op a b) = D.op (turn D a) b := by
    rw [comm a b, turn_commutes_row D comm hc, comm b]
  have diagonal (a : A) : D.op (turn D a) (turn D a) =
      turn D (turn D (D.op a a)) := by
    rw [turn_commutes_row D comm hc, move_left]
  have shift (a : A) : u (turn D a) = turn D (turn D (turn D (u a))) := by
    dsimp only [u]
    rw [diagonal, ← move_left]
    rw [← turn_commutes_row D comm hc, ← turn_commutes_row D comm hc]
  have uid (a : A) : u a = a := by
    obtain ⟨b, rfl⟩ := turn_surjective_of_commutative D comm hc hs a
    rw [shift, turn_twice_right_inverse D comm hc hs]
  have invol (a : A) : turn D (turn D a) = a := by
    have h := turn_twice_right_inverse D comm hc hs a
    change turn D (turn D (u a)) = a at h
    rwa [uid] at h
  have square (a : A) : turn D a = D.op a a := by
    change D.op a (u a) = D.op a a
    rw [uid]
  calc
    turn D x = D.op x x := square x
    _ = turn D (turn D (D.op x x)) := (invol _).symm
    _ = D.op (turn D x) (turn D x) := (diagonal x).symm
    _ = turn D (turn D x) := (square _).symm
    _ = x := invol x

theorem idempotent_of_commutative (hs : Short D) (x : A) : D.op x x = x := by
  have hid := turn_eq_self_of_commutative D comm hc hs
  have htwo := turn_twice_right_inverse D comm hc hs x
  simp only [hid] at htwo
  have hrow : turn D x = D.op x x := congrArg (D.op x) htwo
  exact hrow.symm.trans (hid x)

theorem equation75_of_commutative (hs : Short D) : @Equation75 A D := by
  intro x y
  rw [← turn_eq_row_cube D comm hc x y, turn_eq_self_of_commutative D comm hc hs]

end

/-- Commutative division makes the source square bijective even without
finiteness: it is an inverse to the cube of any division row. -/
theorem common_short_of_commutative_image {A : Type} (D : Magma A)
    (comm : ∀ x y, D.op x y = D.op y x) (h : InImage Law1516 .left D) :
    Common D ∧ Short D := by
  obtain ⟨M, hm, hd⟩ := h
  have hm' := (@Law1516.models_iff A M).mp hm
  have hq := sideQuasigroup_of_division (division_symm hd)
  have cubes (x y : A) : D.op y (D.op y (D.op y (M.op x x))) = x := by
    have hh := cross_square M D hd hm' x y
    unfold cross at hh
    rwa [comm (M.op x x) y] at hh
  have inverse_square (x : A) : M.op (turn D x) (turn D x) = x := by
    apply (hq x).1
    apply (hq x).1
    apply (hq x).1
    exact cubes (turn D x) x
  have hc : Common D := by
    intro x y
    rw [← inverse_square x]
    rw [cross_square M D hd hm']
    exact (cross_square M D hd hm' (turn D x)
      (M.op (turn D x) (turn D x))).symm
  have hf : Fixed D := by
    intro x
    have hh := hd.2 (turn D x) (turn D x)
    rwa [inverse_square] at hh
  exact ⟨hc, short_of_criterion D hq hc hf⟩

/-- An explicit construction for the commutative image: cube-one rows have
inverse equal to their square. Idempotence supplies the source diagonal. -/
theorem image_of_commutative_idempotent75 {A : Type} (D : Magma A)
    (comm : ∀ x y, D.op x y = D.op y x)
    (hi : ∀ x, D.op x x = x) (h75 : @Equation75 A D) :
    InImage Law1516 .left D := by
  let M : Magma A := ⟨fun x y => D.op x (D.op x y)⟩
  have hd : IsDivision .left M D :=
    ⟨fun x y => (h75 y x).symm, fun x y => (h75 y x).symm⟩
  refine ⟨M, (@Law1516.models_iff A M).mpr ?_, hd⟩
  have diagonal (x : A) : M.op x x = x := by
    change D.op x (D.op x x) = x
    rw [hi, hi]
  have twice (x y : A) : M.op x (M.op x y) = D.op x y :=
    (h75 (D.op x y) x).symm
  intro x y
  rw [diagonal, twice]
  change x = D.op y (D.op y (D.op x y))
  rw [comm x y]
  exact h75 x y

/-- Complete arbitrary-carrier classification within the commutative class:
the image consists exactly of idempotent magmas whose rows cube to one. -/
theorem commutative_image_iff_idempotent75 {A : Type} (D : Magma A)
    (comm : ∀ x y, D.op x y = D.op y x) :
    InImage Law1516 .left D ↔ (∀ x, D.op x x = x) ∧ @Equation75 A D := by
  constructor
  · intro h
    obtain ⟨hc, hs⟩ := common_short_of_commutative_image D comm h
    exact ⟨idempotent_of_commutative D comm hc hs,
      equation75_of_commutative D comm hc hs⟩
  · rintro ⟨hi, h75⟩
    exact image_of_commutative_idempotent75 D comm hi h75

/-- The proposed pair is exact in the commutative class on every carrier. -/
theorem characterizes_commutative {A : Type} (D : Magma A)
    (comm : ∀ x y, D.op x y = D.op y x) :
    (Common D ∧ Short D) ↔ InImage Law1516 .left D := by
  constructor
  · rintro ⟨hc, hs⟩
    exact image_of_commutative_idempotent75 D comm
      (idempotent_of_commutative D comm hc hs)
      (equation75_of_commutative D comm hc hs)
  · exact common_short_of_commutative_image D comm

/-- Exact finite characterization within the commutative class. This is
not an unconditional catalogue characterization. -/
theorem characterizes_commutative_fin {A : Type} [Finite A] (D : Magma A)
    (comm : ∀ x y, D.op x y = D.op y x) :
    (Common D ∧ Short D) ↔ InImage Law1516 .left D :=
  characterizes_commutative D comm

end Parastrophes.Eq1516Image
