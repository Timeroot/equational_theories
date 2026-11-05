import equational_theories.Parastrophes.Equation910Image
import equational_theories.Parastrophes.ReductionImageObstructions
import Mathlib.Data.Fin.VecNotation

/-!
# E910's division image has no equational characterization, even finitely

An actual left-division image of E910 is exactly a left quasigroup satisfying
E427. This file constructs a seven-part integer operation

    D((i,u),(j,v)) = (colour(i,j), left(i,j)*u + right(i,j)*v).

Its 49 coefficient equations prove E427 over every commutative ring. Every
base row is a permutation, and the right coefficients are ±1 except for one
entry -2. Therefore reduction modulo any odd prime has bijective rows and is
an actual E910 division image. Reduction modulo two is a 14-element nonimage:
its row at (1,0) identifies (3,0) and (3,1).

Suppose an arbitrary magma equation holds in every finite image. It holds in
all odd-prime reductions above. For any integer assignment, the difference of
the two evaluated integer coordinates is divisible by every odd prime, hence
zero; the equation therefore holds in the integer operation. Surjectivity of
reduction then transfers it to the bad 14-element operation. Thus that one
nonimage satisfies *every* equation common to the finite images. No set of
magma equations, in particular no single equation of any size, characterizes
the image among finite magmas or among arbitrary magmas.

The finite data checks comprise 49 coefficient identities, seven base-row
permutations, and one explicit collision. The unbounded equation-transfer
argument is ordinary mathematics in Lean; no model-search certificate,
native evaluation, or additional axiom is used.
-/

namespace Parastrophes.Eq910SingularImage
open Law FreeMagma

def colour : Fin 7 → Fin 7 → Fin 7 := ![
  ![2, 1, 0, 3, 5, 4, 6],
  ![3, 2, 6, 4, 0, 1, 5],
  ![0, 1, 2, 3, 4, 5, 6],
  ![5, 4, 3, 2, 1, 0, 6],
  ![0, 1, 4, 5, 2, 3, 6],
  ![0, 1, 5, 3, 4, 2, 6],
  ![0, 5, 6, 3, 4, 1, 2]]

def left : Fin 7 → Fin 7 → Int := ![
  ![1, -1, 1, 0, -2, -2, 0],
  ![0, -1, -1, 0, 0, 1, 1],
  ![1, 1, 1, 0, -1, -1, 1],
  ![2, -1, 1, 1, 1, 2, 1],
  ![0, 0, 1, -1, 1, -1, 0],
  ![-1, 0, 1, 0, 1, -1, 0],
  ![0, -1, 1, 0, 1, -1, 1]]

def right : Fin 7 → Fin 7 → Int := ![
  ![-1, -1, -1, 1, -1, -1, 1],
  ![1, 1, -1, -2, -1, -1, 1],
  ![-1, -1, -1, 1, -1, -1, -1],
  ![-1, 1, -1, -1, 1, -1, -1],
  ![1, 1, -1, -1, -1, -1, 1],
  ![-1, 1, 1, 1, -1, 1, 1],
  ![1, -1, -1, 1, -1, -1, -1]]

@[implicit_reducible] def family (R : Type) [CommRing R] : Magma (Fin 7 × R) :=
  ⟨fun x y => (colour x.1 y.1, (left x.1 y.1 : R)*x.2 + (right x.1 y.1 : R)*y.2)⟩

/-- The integer certificate enumerates only 49 pairs of parts. -/
theorem coefficient_certificate : ∀ i j : Fin 7,
    let k := colour i j
    let l := colour i k
    let m := colour j l
    colour i m=i ∧
    left i m+right i m*right j l*(left i k+right i k*left i j)=1 ∧
    left j l+right j l*right i k*right i j=0 := by decide

theorem equation427 (R : Type) [CommRing R] : @Equation427 (Fin 7 × R) (family R) := by
  intro ⟨i,u⟩ ⟨j,v⟩
  let k := colour i j
  let l := colour i k
  let m := colour j l
  obtain ⟨hcol,ha,hb⟩ := coefficient_certificate i j
  change colour i m=i at hcol
  change left i m+right i m*right j l*(left i k+right i k*left i j)=1 at ha
  change left j l+right j l*right i k*right i j=0 at hb
  have hA : (left i m:R)+(right i m:R)*(right j l:R)*
      ((left i k:R)+(right i k:R)*(left i j:R))=1 := by
    simpa only [map_add,map_mul,map_one] using congrArg (Int.castRingHom R) ha
  have hB : (left j l:R)+(right j l:R)*(right i k:R)*(right i j:R)=0 := by
    simpa only [map_add,map_mul,map_zero] using congrArg (Int.castRingHom R) hb
  apply Prod.ext
  · exact hcol.symm
  · change u = (left i m:R)*u+(right i m:R)*((left j l:R)*v+
      (right j l:R)*((left i k:R)*u+(right i k:R)*((left i j:R)*u+(right i j:R)*v)))
    linear_combination -u*hA-(right i m:R)*v*hB

theorem colour_bijective : ∀ i, Function.Bijective (colour i) := by decide

theorem right_values : ∀ i j, right i j=1 ∨ right i j= -1 ∨ right i j= -2 := by decide

theorem right_ne_zero (R : Type) [Field R] (h2 : (2:R) ≠ 0) (i j : Fin 7) :
    (right i j:R) ≠ 0 := by
  rcases right_values i j with h | h | h <;> rw [h]
  · simp
  · simp
  · simpa using neg_ne_zero.mpr h2

theorem rows (R : Type) [Field R] (h2 : (2:R) ≠ 0) : IsSideQuasigroup .left (family R) := by
  rintro ⟨i,u⟩
  constructor
  · rintro ⟨j,v⟩ ⟨k,w⟩ he
    have hc := congrArg Prod.fst he
    change colour i j=colour i k at hc
    have hidx := (colour_bijective i).1 hc
    subst k
    have hf := congrArg Prod.snd he
    change (left i j:R)*u+(right i j:R)*v=(left i j:R)*u+(right i j:R)*w at hf
    have hw := mul_left_cancel₀ (right_ne_zero R h2 i j) (add_left_cancel hf)
    exact Prod.ext rfl hw
  · rintro ⟨k,w⟩
    obtain ⟨j,hj⟩ := (colour_bijective i).2 k
    refine ⟨(j,(w-(left i j:R)*u)/(right i j:R)),Prod.ext hj ?_⟩
    change (left i j:R)*u+(right i j:R)*((w-(left i j:R)*u)/(right i j:R))=w
    rw [mul_div_cancel₀ _ (right_ne_zero R h2 i j)]
    ring

theorem prime_inImage (p : Nat) (hp : p.Prime) (hp2 : 2 < p) :
    InImage Law910 .left (family (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact (Eq910Image.inImage_iff _).mpr
    ⟨equation427 _,rows _ (ReductionImage.two_ne_zero hp2)⟩

theorem bad_collision :
    (family (ZMod 2)).op (1,0) (3,0)=(family (ZMod 2)).op (1,0) (3,1) := by decide

theorem bad_not_leftQuasigroup : ¬ IsSideQuasigroup .left (family (ZMod 2)) := by
  intro h
  have he := (h (1,0)).1 bad_collision
  have hh : (0:ZMod 2)=1 := congrArg Prod.snd he
  exact zero_ne_one hh

def reduce (n : Nat) (x : Fin 7 × Int) : Fin 7 × ZMod n := (x.1,(x.2:Int))

theorem reduce_op (n : Nat) (x y : Fin 7 × Int) :
    reduce n ((family Int).op x y)=(family (ZMod n)).op (reduce n x) (reduce n y) := by
  apply Prod.ext
  · rfl
  · change ((left x.1 y.1*x.2+right x.1 y.1*y.2:Int):ZMod n)=
      (left x.1 y.1:ZMod n)*(x.2:ZMod n)+(right x.1 y.1:ZMod n)*(y.2:ZMod n)
    simp only [Int.cast_add,Int.cast_mul]

theorem eval_reduce (n : Nat) (t : FreeMagma Nat) (v : Nat → Fin 7 × Int) :
    reduce n (@evalInMagma _ _ (family Int) v t)=
      @evalInMagma _ _ (family (ZMod n)) (fun i => reduce n (v i)) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => exact (reduce_op n _ _).trans (congrArg₂ (family (ZMod n)).op ha hb)

/-- Any common equation of all odd-prime images first lifts to the integers. -/
theorem integer_of_odd_primes {K : NatMagmaLaw}
    (h : ∀ p : Nat, p.Prime → 2<p → @satisfies _ _ (family (ZMod p)) K) :
    @satisfies _ _ (family Int) K := by
  intro v
  have he (p : Nat) (hp : p.Prime) (hp2 : 2<p) :
      reduce p (@evalInMagma _ _ (family Int) v K.lhs)=
        reduce p (@evalInMagma _ _ (family Int) v K.rhs) :=
    (eval_reduce p K.lhs v).trans ((h p hp hp2 _).trans (eval_reduce p K.rhs v).symm)
  apply Prod.ext
  · exact congrArg (fun z : Fin 7 × ZMod 3 => z.1) (he 3 (by decide) (by decide))
  · apply ReductionImage.int_eq_of_prime_reductions
    intro p hp hp2
    exact congrArg Prod.snd (he p hp hp2)

/-- Reduction modulo two transfers every equation, with no bound on its size. -/
theorem mod_two_of_integer {K : NatMagmaLaw} (h : @satisfies _ _ (family Int) K) :
    @satisfies _ _ (family (ZMod 2)) K := by
  intro v
  let w : Nat → Fin 7 × Int := fun i => ((v i).1,((v i).2.val:Int))
  have hw (i) : reduce 2 (w i)=v i := by simp [w,reduce]
  have he := congrArg (reduce 2) (h w)
  rw [eval_reduce,eval_reduce] at he
  simpa only [hw] using he

/-- The 14-element nonimage satisfies every equation shared by the finite
E910 left-division images. This is stronger than excluding a single equation. -/
theorem bad_inherits {K : NatMagmaLaw}
    (h : ∀ (A : Type) [Finite A] (D : Magma A), InImage Law910 .left D →
      @satisfies _ A D K) : @satisfies _ _ (family (ZMod 2)) K := by
  apply mod_two_of_integer
  apply integer_of_odd_primes
  intro p hp hp2
  letI : Fact p.Prime := ⟨hp⟩
  exact h _ _ (prime_inImage p hp hp2)

end Parastrophes.Eq910SingularImage

namespace Parastrophes.Catalogue
open Law

/-- A singular affine family defeats every putative finite image equation. -/
@[parastrophe_result] theorem left_noSingleEquation910_fin :
    ¬ SingleEquation .fin Law910 .left := by
  rintro ⟨K,hK⟩
  have hbad := Eq910SingularImage.bad_inherits (K:=K) (by
    intro A hA D hd
    exact (hK A D hA).mpr hd)
  exact Eq910SingularImage.bad_not_leftQuasigroup
    (characterizes_sideQuasigroup hK _ _ (inferInstance : Finite (Fin 7 × ZMod 2)) hbad)

/-- An arbitrary-carrier characterization would also characterize finite images. -/
@[parastrophe_result] theorem left_noSingleEquation910_all :
    ¬ SingleEquation .all Law910 .left :=
  fun h => left_noSingleEquation910_fin (singleEquation_finite h)

end Parastrophes.Catalogue
