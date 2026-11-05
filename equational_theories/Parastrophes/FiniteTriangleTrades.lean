import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Finite replacements in a zero-sum triangle partition

The map J(u,v)=(-v,u-v) partitions V×V into zero-sum cycles of length
dividing three. Three disjoint J-orbits can be rearranged: replace the
column triples of a 3×3 array by its row triples. If a+b+c=0, the new
triples (a,b,c), (Ja,Jb,Jc), and (J²a,J²b,J²c) also sum to zero.

This lemma performs any disjoint family of such replacements. It preserves
the carrier, so a finite additive group gives a finite construction. In
particular it does not require a finite version of an infinite greedy
completion theorem.
-/
namespace Parastrophes.FiniteTriangleTrades

def next (i : Fin 3) : Fin 3 := i + 1

@[simp] theorem next_three (i : Fin 3) : next (next (next i)) = i := by
  fin_cases i <;> decide

variable {V : Type*} [AddCommGroup V]

def axis (v : V) (i : Fin 3) : V × V :=
  if i = 0 then (v,0) else if i = 1 then (0,v) else (-v,-v)

def rotate (x : V × V) : V × V := (-x.2, x.1-x.2)

theorem rotate_three (x : V × V) : rotate (rotate (rotate x)) = x := by
  apply Prod.ext <;> simp [rotate]
  abel

theorem rotate_injective : Function.Injective (rotate (V := V)) := by
  intro x y h
  calc
    x = rotate (rotate (rotate x)) := (rotate_three x).symm
    _ = rotate (rotate (rotate y)) := congrArg (fun z => rotate (rotate z)) h
    _ = y := rotate_three y

theorem rotate_sum (x : V × V) : x + rotate (rotate x) + rotate x = 0 := by
  apply Prod.ext <;> simp [rotate]
  abel

theorem rotate_axis (v : V) (i : Fin 3) : rotate (axis v i) = axis v (next i) := by
  fin_cases i <;> simp [rotate, axis, next]

theorem axis_zero (i : Fin 3) : axis (0 : V) i = 0 := by
  fin_cases i <;> simp [axis]

theorem axis_add (v w : V) (i : Fin 3) : axis (v+w) i = axis v i + axis w i := by
  fin_cases i <;> simp [axis, add_comm]

theorem axis_eq {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) (i j : Fin 3)
    (he : axis v i = axis w j) : v = w ∧ i = j := by
  fin_cases i <;> fin_cases j <;> simp [axis, Prod.mk.injEq] at he ⊢
  all_goals aesop

variable {B : Type*}

def point (f : B → Fin 3 → V) (z : (B × Fin 3) × Fin 3) : V × V :=
  axis (f z.1.1 z.1.2) z.2

def step (z : (B × Fin 3) × Fin 3) := ((z.1.1, next z.1.2), z.2)

theorem point_injective (f : B → Fin 3 → V)
    (hi : Function.Injective (fun z : B × Fin 3 => f z.1 z.2))
    (hn : ∀ b i, f b i ≠ 0) : Function.Injective (point f) := by
  intro x y he
  obtain ⟨hv, ha⟩ := axis_eq (hn x.1.1 x.1.2) (hn y.1.1 y.1.2) x.2 y.2 he
  exact Prod.ext (hi hv) ha

/-- Preserve the default rotation off the supplied blocks, and rotate each
new zero-sum row within its block. -/
theorem exists_turn (f : B → Fin 3 → V)
    (hi : Function.Injective (fun z : B × Fin 3 => f z.1 z.2))
    (hn : ∀ b i, f b i ≠ 0)
    (hs : ∀ b, f b 0 + f b 1 + f b 2 = 0) :
    ∃ s : V × V → V × V,
      (∀ x, s (s (s x)) = x) ∧
      (∀ x, x + s (s x) + s x = 0) ∧
      (∀ b, s (f b 0, 0) = (f b 1, 0)) := by
  classical
  let E := point f
  have hE : Function.Injective E := point_injective f hi hn
  let s := fun x => if h : ∃ z, E z = x then E (step (Classical.choose h)) else rotate x
  have hon (z) : s (E z) = E (step z) := by
    dsimp only [s]
    have hz : ∃ w, E w = E z := ⟨z,rfl⟩
    rw [dif_pos hz]
    exact congrArg (fun w => E (step w)) (hE (Classical.choose_spec hz))
  have hout (x) (hx : ¬ ∃ z, E z = x) : ¬ ∃ z, E z = rotate x := by
    rintro ⟨z,hz⟩
    apply hx
    refine ⟨(z.1, next (next z.2)), ?_⟩
    apply rotate_injective
    change rotate (axis (f z.1.1 z.1.2) (next (next z.2))) = rotate x
    rw [rotate_axis, next_three]
    exact hz
  have hoff (x) (hx : ¬ ∃ z, E z = x) : s x = rotate x := dif_neg hx
  have hsum (b) (i : Fin 3) : f b i + f b (next (next i)) + f b (next i) = 0 := by
    calc
      _ = f b 0 + f b 1 + f b 2 := by fin_cases i <;> simp [next] <;> abel
      _ = 0 := hs b
  have hpoint (z) : E z + E (step (step z)) + E (step z) = 0 := by
    change axis (f z.1.1 z.1.2) z.2 +
      axis (f z.1.1 (next (next z.1.2))) z.2 +
      axis (f z.1.1 (next z.1.2)) z.2 = 0
    rw [← axis_add, ← axis_add, hsum, axis_zero]
  refine ⟨s, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : ∃ z, E z = x
    · obtain ⟨z,rfl⟩ := hx
      rw [hon, hon, hon]
      simp [step]
    · rw [hoff x hx, hoff _ (hout x hx), hoff _ (hout _ (hout x hx))]
      exact rotate_three x
  · intro x
    by_cases hx : ∃ z, E z = x
    · obtain ⟨z,rfl⟩ := hx
      rw [hon, hon]
      exact hpoint z
    · rw [hoff x hx, hoff _ (hout x hx)]
      exact rotate_sum x
  · intro b
    simpa [E, point, axis, step, next] using hon ((b,0),0)

/-- A version indexed by all points in a union of cycles, avoiding a choice
of cycle representatives. It is useful when transferring a finite fragment
of an infinite turn into a finite additive group. -/
theorem exists_turn_on_points (f : B → V) (p : B → B)
    (hi : Function.Injective f) (hn : ∀ b, f b ≠ 0)
    (hc : ∀ b, p (p (p b))=b)
    (hs : ∀ b, f b + f (p b) + f (p (p b)) = 0) :
    ∃ t : V × V → V × V,
      (∀ x, t (t (t x))=x) ∧
      (∀ x, x+t x+t (t x)=0) ∧
      (∀ b, t (f b,0)=(f (p b),0)) := by
  classical
  let E := fun z : B × Fin 3 => axis (f z.1) z.2
  let P := fun z : B × Fin 3 => (p z.1,z.2)
  have hE : Function.Injective E := by
    intro x y he
    obtain ⟨he,hij⟩ := axis_eq (hn x.1) (hn y.1) x.2 y.2 he
    exact Prod.ext (hi he) hij
  let t := fun x => if h : ∃ z, E z=x then E (P (Classical.choose h)) else rotate x
  have hon (z) : t (E z)=E (P z) := by
    dsimp only [t]
    have hz : ∃ w, E w=E z := ⟨z,rfl⟩
    rw [dif_pos hz]
    exact congrArg (fun z => E (P z)) (hE (Classical.choose_spec hz))
  have hout (x) (hx : ¬ ∃ z, E z=x) : ¬ ∃ z, E z=rotate x := by
    rintro ⟨z,hz⟩
    apply hx
    refine ⟨(z.1,next (next z.2)),?_⟩
    apply rotate_injective
    change rotate (axis (f z.1) (next (next z.2)))=rotate x
    rw [rotate_axis,next_three]
    exact hz
  have hoff (x) (hx : ¬ ∃ z, E z=x) : t x=rotate x := dif_neg hx
  refine ⟨t,?_,?_,?_⟩
  · intro x
    by_cases hx : ∃ z, E z=x
    · obtain ⟨z,rfl⟩ := hx
      rw [hon,hon,hon]
      simp [P,hc]
    · rw [hoff x hx,hoff _ (hout x hx),hoff _ (hout _ (hout x hx))]
      exact rotate_three x
  · intro x
    by_cases hx : ∃ z, E z=x
    · obtain ⟨z,rfl⟩ := hx
      rw [hon,hon]
      change axis (f z.1) z.2 + axis (f (p z.1)) z.2 + axis (f (p (p z.1))) z.2=0
      rw [← axis_add,← axis_add,hs,axis_zero]
    · rw [hoff x hx,hoff _ (hout x hx)]
      have he := rotate_sum x
      calc
        _ = x+rotate (rotate x)+rotate x := by abel
        _ = 0 := he
  · intro b
    simpa [E,P,axis] using hon (b,0)

end Parastrophes.FiniteTriangleTrades
