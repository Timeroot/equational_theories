import equational_theories.Parastrophes.FiniteTriangleTrades
import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All
import Mathlib.Data.ZMod.Basic

/-!
# E115 models with arbitrarily long square cycles

Suppose A is a permutation made of oriented triangles, with
`x + A(x) + A²(x) = -s` and `A(0)=s`. Then `M(x,y)=y+A(y-x)` satisfies
E115 and has square map `x ↦ x+s`.

For a concrete finite construction, start with the order-three rotation on
`(Z/nZ)²`. Trade the three orbits through (1,0), (4,0), and (-5,0) to make
these three points one cycle. Conjugate the resulting turn by translation
through (1,0). This gives s=(3,0), for every n>10. Consequently the square map
has no fixed positive period valid in all finite E115 models.

Only nine distinguished points are used; there are no multiplication tables
or model-search certificates. This rules out a period-based recovery shortcut,
not arbitrary recovery terms or single-equation image characterizations.
-/
namespace Parastrophes.Eq115SquareTranslations

@[implicit_reducible] def source {G : Type*} [AddCommGroup G] (A : G → G) : Magma G :=
  ⟨fun x y => y + A (y-x)⟩

@[implicit_reducible] def rightDivision {G : Type*} [AddCommGroup G]
    (A : G → G) : Magma G := ⟨fun x y => y - A (A (x-y))⟩

/-- This explicit division operation is useful for further image research;
it uses the turn twice and does not iterate the square map. -/
theorem isRightDivision {G : Type*} [AddCommGroup G] (A : G → G)
    (h3 : ∀ x, A (A (A x)) = x) :
    IsDivision .right (source A) (rightDivision A) := by
  constructor <;> intro x y
  · change y + A (y-(y-A (A (x-y)))) = x
    rw [sub_sub_cancel, h3]
    abel
  · change y - A (A ((y+A (y-x))-y)) = x
    rw [add_sub_cancel_left, h3]
    abel

theorem square {G : Type*} [AddCommGroup G] (A : G → G) (s : G)
    (h0 : A 0 = s) (x : G) : (source A).op x x = x+s := by
  change x + A (x-x) = x+s
  rw [sub_self, h0]

/-- The triangle-sum identity is exactly what is needed for E115. -/
theorem source_law {G : Type*} [AddCommGroup G] (A : G → G) (s : G)
    (h0 : A 0 = s) (ht : ∀ x, x + A x + A (A x) = -s) :
    @Equation115 G (source A) := by
  intro x y
  rw [square A s h0]
  change x = (y + A (y-(x+s))) + A ((y + A (y-(x+s)))-y)
  rw [add_sub_cancel_left]
  have he := ht (y-(x+s))
  calc
    x = x+s+(y-(x+s) + A (y-(x+s)) + A (A (y-(x+s)))) := by rw [he]; abel
    _ = _ := by abel

/-- The same triangle construction, with multiplication reversed, also
satisfies E873. This is a property of the construction, not a claimed
implication between all E115 and E873 magmas. -/
theorem opposite_source_law873 {G : Type*} [AddCommGroup G] (A : G → G) (s : G)
    (h0 : A 0=s) (ht : ∀ x, x+A x+A (A x)= -s)
    (h3 : ∀ x, A (A (A x))=x) : @Equation873 G (opposite (source A)) := by
  intro x y
  change x = y+A (y-((x+A (x-x))+A ((x+A (x-x))-(y+A (y-y)))))
  rw [sub_self,sub_self,h0]
  have he : (x+s)-(y+s)=x-y := by abel
  rw [he]
  have harg : y-(x+s+A (x-y))=A (A (x-y)) := by
    have hh := ht (x-y)
    calc
      _ = A (A (x-y)) - ((x-y)+A (x-y)+A (A (x-y))+s) := by abel
      _ = A (A (x-y)) := by rw [hh]; abel
  rw [harg,h3]
  abel

private def coefficient (i : Fin 3) : ℕ := if i=0 then 6 else if i=1 then 9 else 0

private theorem coefficient_injective : Function.Injective coefficient := by decide

private theorem cast_injective_below (n a b : ℕ) (ha : a<n) (hb : b<n)
    (he : (a : ZMod n) = b) : a=b := by
  have hh := congrArg ZMod.val he
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hh

/-- A fixed nine-point trade works modulo every n>10. -/
theorem exists_model (n : ℕ) (hn : 10<n) :
    ∃ M : Magma (ZMod n × ZMod n), @Equation115 _ M ∧
      ∀ x, M.op x x = x + (3,0) := by
  let f : Fin 3 → ZMod n := fun i => coefficient i - 5
  have hc (i : Fin 3) : coefficient i < n := by
    fin_cases i <;> simp [coefficient] <;> omega
  have hi : Function.Injective f := by
    intro i j he
    apply coefficient_injective
    exact cast_injective_below n _ _ (hc i) (hc j) (sub_left_inj.mp he)
  have hzero (i : Fin 3) : f i ≠ 0 := by
    intro he
    have he' : (coefficient i : ZMod n) = (5 : ℕ) := sub_eq_zero.mp he
    have hh := cast_injective_below n _ _ (hc i) (by omega) he'
    fin_cases i <;> norm_num [coefficient] at hh
  have hib : Function.Injective (fun z : Unit × Fin 3 => f z.2) := by
    intro x y he
    exact Prod.ext (Subsingleton.elim _ _) (hi he)
  have hf0 : f 0 = 1 := by change (6:ZMod n)-5=1; ring
  have hf1 : f 1 = 4 := by change (9:ZMod n)-5=4; ring
  have hf2 : f 2 = -5 := by
    simp [f, coefficient, show (2:Fin 3) ≠ 0 by decide, show (2:Fin 3) ≠ 1 by decide]
  have hsum (_ : Unit) : f 0 + f 1 + f 2 = 0 := by
    rw [hf0, hf1, hf2]
    ring
  obtain ⟨t, _, ht, hs⟩ := FiniteTriangleTrades.exists_turn
    (fun _ : Unit => f) hib (fun _ => hzero) hsum
  have ht0 : t (1,0) = (4,0) := by
    simpa only [hf0, hf1] using hs ()
  let v : ZMod n × ZMod n := (1,0)
  let A := fun x => t (x+v)-v
  have h0 : A 0 = (3,0) := by
    norm_num [A, v, ht0]
  have htri (x : ZMod n × ZMod n) : x + A x + A (A x) = -(3,0) := by
    have he := ht (x+v)
    change x+v + t (t (x+v)) + t (x+v) = 0 at he
    dsimp only [A]
    rw [sub_add_cancel]
    calc
      x + (t (x+v)-v) + (t (t (x+v))-v) =
          (x+v+t (t (x+v))+t (x+v)) - (v+v+v) := by abel
      _ = -(3,0) := by rw [he]; simp [v]; norm_num
  exact ⟨source A, source_law A (3,0) h0 htri, square A (3,0) h0⟩

theorem square_iterate {G : Type*} [AddCommGroup G] (M : Magma G) (s : G)
    (hs : ∀ x, M.op x x = x+s) (k : ℕ) (x : G) :
    (fun y => M.op y y)^[k] x = x + k • s := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', hs, ih, succ_nsmul]; abel

/-- In particular, no positive exponent is a square-map identity of the
entire class of finite E115 models. -/
theorem no_uniform_square_period (k : ℕ) (hk : 0<k) :
    ∃ (G : Type) (_ : Finite G) (M : Magma G) (x : G),
      @Equation115 G M ∧ (fun y => M.op y y)^[k] x ≠ x := by
  let n := 3*k+11
  have hn : 10<n := by dsimp [n]; omega
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨M, hm, hs⟩ := exists_model n hn
  refine ⟨ZMod n × ZMod n, inferInstance, M, (0,0), hm, ?_⟩
  rw [square_iterate M (3,0) hs]
  intro he
  have hz : (3*k : ZMod n) = 0 := by
    have hh := congrArg Prod.fst he
    simpa [nsmul_eq_mul, mul_comm] using hh
  have hd : n ∣ 3*k := (ZMod.natCast_eq_zero_iff (3*k) n).mp (by simpa using hz)
  have hh := Nat.le_of_dvd (by omega : 0<3*k) hd
  dsimp [n] at hh
  omega

end Parastrophes.Eq115SquareTranslations
