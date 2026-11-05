import equational_theories.Parastrophes.FiniteTriangleTrades
import Mathlib.Tactic.Group

/-!
# Triangle trades over a noncommutative group

The default turn on H × H is J(a,b)=(b,a⁻¹b⁻¹). It has order three
and satisfies x J²(x) J(x)=1. To modify it at x=(a,b), choose c and put

    y=(c,a⁻¹b⁻¹cb⁻¹),       z=(a⁻¹c⁻¹,c⁻¹ba).

Each of (x,y,z), (Jx,Jy,Jz), and (J²x,J²y,J²z) is an oriented group
triangle: first times third times second is 1. Replacing the three column
orbits by these three rows gives a new turn with the same two identities.
The lemma below performs any disjoint family of such nine-point trades.
It works in finite groups too; it makes no commutativity assumption.
-/
namespace Parastrophes.GroupTriangleTrades
open FiniteTriangleTrades (next next_three)
variable {H : Type*} [Group H]

def rotate (x : H × H) : H × H := (x.2, x.1⁻¹ * x.2⁻¹)

theorem rotate_three (x : H × H) : rotate (rotate (rotate x)) = x := by
  apply Prod.ext <;> simp [rotate]

theorem rotate_triangle (x : H × H) : x * rotate (rotate x) * rotate x = 1 := by
  apply Prod.ext <;> simp [rotate]

theorem rotate_injective : Function.Injective (rotate (H := H)) := by
  intro x y h
  calc
    x = rotate (rotate (rotate x)) := (rotate_three x).symm
    _ = rotate (rotate (rotate y)) := congrArg (fun z => rotate (rotate z)) h
    _ = y := rotate_three y

def orbit (x : H × H) (i : Fin 3) : H × H :=
  if i = 0 then x else if i = 1 then rotate x else rotate (rotate x)

theorem rotate_orbit (x : H × H) (i : Fin 3) :
    rotate (orbit x i) = orbit x (next i) := by
  fin_cases i <;> simp [orbit, next, rotate_three]

/-- Equality of two orbit points puts the first base point in the second orbit. -/
theorem orbit_back {x y : H × H} (i j : Fin 3) (he : orbit x i = orbit y j) :
    ∃ k : Fin 3, x = orbit y k := by
  fin_cases i
  · exact ⟨j,he⟩
  · refine ⟨next (next j),?_⟩
    change rotate x = orbit y j at he
    have h := congrArg (fun z => rotate (rotate z)) he
    simpa only [rotate_three,rotate_orbit] using h
  · refine ⟨next j,?_⟩
    change rotate (rotate x) = orbit y j at he
    have h := congrArg rotate he
    simpa only [rotate_three,rotate_orbit] using h

theorem orbit_injective {x : H × H} (h1 : x ≠ rotate x) (h2 : x ≠ rotate (rotate x)) :
    Function.Injective (orbit x) := by
  intro i j he
  have h12 : rotate x ≠ rotate (rotate x) := fun h => h1 (rotate_injective h)
  fin_cases i <;> fin_cases j <;> simp [orbit] at he ⊢
  all_goals first | exact (h1 he).elim | exact (h1 he.symm).elim |
    exact (h2 he).elim | exact (h2 he.symm).elim |
    exact (h12 he).elim | exact (h12 he.symm).elim

def row (x : H × H) (c : H) (i : Fin 3) : H × H :=
  if i = 0 then x else if i = 1 then
    (c, x.1⁻¹ * x.2⁻¹ * c * x.2⁻¹) else
    (x.1⁻¹ * c⁻¹, c⁻¹ * x.2 * x.1)

/-- All three row triangles, including their cyclic starting points. -/
theorem row_triangle (x : H × H) (c : H) (i j : Fin 3) :
    orbit (row x c i) j * orbit (row x c (next (next i))) j *
      orbit (row x c (next i)) j = 1 := by
  fin_cases i <;> fin_cases j <;> apply Prod.ext <;>
    simp [orbit, row, next, rotate] <;> group

variable {B : Type*}

def point (x : B → H × H) (c : B → H) (z : (B × Fin 3) × Fin 3) : H × H :=
  orbit (row (x z.1.1) (c z.1.1) z.1.2) z.2

/-- Group homomorphisms preserve all the formulas defining a trade. -/
theorem map_point {K : Type*} [Group K] (f : H →* K)
    (x : B → H × H) (c : B → H) (z : (B × Fin 3) × Fin 3) :
    point (fun b => (f (x b).1,f (x b).2)) (fun b => f (c b)) z =
      (f (point x c z).1,f (point x c z).2) := by
  rcases z with ⟨⟨b,i⟩,j⟩
  fin_cases i <;> fin_cases j <;> simp [point,orbit,row,rotate,map_mul,map_inv]

def step (z : (B × Fin 3) × Fin 3) := ((z.1.1, next z.1.2), z.2)

/-- A disjoint family of trades preserves the carrier and gives the stated
second iterate at each designated input. -/
theorem exists_turn (x : B → H × H) (c : B → H)
    (hi : Function.Injective (point x c)) :
    ∃ s : H × H → H × H,
      (∀ a, s (s (s a)) = a) ∧
      (∀ a, a * s (s a) * s a = 1) ∧
      (∀ b, s (s (x b)) = ((x b).1⁻¹ * (c b)⁻¹, (c b)⁻¹ * (x b).2 * (x b).1)) := by
  classical
  let E := point x c
  let s := fun a => if h : ∃ z, E z = a then E (step (Classical.choose h)) else rotate a
  have hon (z) : s (E z) = E (step z) := by
    dsimp only [s]
    have hz : ∃ w, E w = E z := ⟨z,rfl⟩
    rw [dif_pos hz]
    exact congrArg (fun w => E (step w)) (hi (Classical.choose_spec hz))
  have hout (a) (ha : ¬ ∃ z, E z = a) : ¬ ∃ z, E z = rotate a := by
    rintro ⟨z,hz⟩
    apply ha
    refine ⟨(z.1,next (next z.2)),?_⟩
    apply rotate_injective
    change rotate (orbit (row (x z.1.1) (c z.1.1) z.1.2) (next (next z.2))) = rotate a
    rw [rotate_orbit, next_three]
    exact hz
  have hoff (a) (ha : ¬ ∃ z, E z = a) : s a = rotate a := dif_neg ha
  refine ⟨s,?_,?_,?_⟩
  · intro a
    by_cases ha : ∃ z, E z = a
    · obtain ⟨z,rfl⟩ := ha
      rw [hon,hon,hon]
      simp [step]
    · rw [hoff a ha,hoff _ (hout a ha),hoff _ (hout _ (hout a ha))]
      exact rotate_three a
  · intro a
    by_cases ha : ∃ z, E z = a
    · obtain ⟨z,rfl⟩ := ha
      rw [hon,hon]
      exact row_triangle (x z.1.1) (c z.1.1) z.1.2 z.2
    · rw [hoff a ha,hoff _ (hout a ha)]
      exact rotate_triangle a
  · intro b
    have he : x b = E ((b,0),0) := by simp [E,point,orbit,row]
    rw [he,hon,hon]
    simp [E,point,step,orbit,row,next]

end Parastrophes.GroupTriangleTrades
