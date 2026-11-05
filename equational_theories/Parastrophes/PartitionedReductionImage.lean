import equational_theories.Parastrophes.ReductionImageObstructions

/-!
# Singular reduction for affine operations on finitely many parts

The part of an element is retained under reduction; its integer coordinate
is reduced modulo a prime. If every odd-prime reduction is a division image,
every equation shared by those images also holds in the reduction modulo two.
Thus a row collision there rules out an equational characterization of the
finite image, with no bound on the length or number of proposed equations.
-/

namespace Parastrophes.PartitionedReductionImage
open Law FreeMagma

variable {B : Type} (colour : B → B → B) (left right : B → B → Int)

@[implicit_reducible] def family (R : Type) [CommRing R] : Magma (B × R) :=
  ⟨fun x y => (colour x.1 y.1, (left x.1 y.1 : R) * x.2 + (right x.1 y.1 : R) * y.2)⟩

theorem family_op (R : Type) [CommRing R] (x y : B × R) :
    (family colour left right R).op x y =
      (colour x.1 y.1, (left x.1 y.1 : R) * x.2 + (right x.1 y.1 : R) * y.2) := rfl

def reduce (n : Nat) (x : B × Int) : B × ZMod n := (x.1, (x.2 : Int))

theorem reduce_op (n : Nat) (x y : B × Int) :
    reduce n ((family colour left right Int).op x y) =
      (family colour left right (ZMod n)).op (reduce n x) (reduce n y) := by
  apply Prod.ext
  · rfl
  · change ((left x.1 y.1 * x.2 + right x.1 y.1 * y.2 : Int) : ZMod n) = _
    simp only [Int.cast_add, Int.cast_mul]
    rfl

theorem eval_reduce (n : Nat) (t : FreeMagma Nat) (v : Nat → B × Int) :
    reduce n (@evalInMagma _ _ (family colour left right Int) v t) =
      @evalInMagma _ _ (family colour left right (ZMod n)) (fun i => reduce n (v i)) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    exact (reduce_op colour left right n _ _).trans
      (congrArg₂ (family colour left right (ZMod n)).op ha hb)

/-- Lift an arbitrary common equation to the integer operation. -/
theorem integer_of_odd_primes {K : NatMagmaLaw}
    (h : ∀ p : Nat, p.Prime → 2 < p →
      @satisfies _ _ (family colour left right (ZMod p)) K) :
    @satisfies _ _ (family colour left right Int) K := by
  intro v
  have he (p : Nat) (hp : p.Prime) (hp2 : 2 < p) :
      reduce p (@evalInMagma _ _ (family colour left right Int) v K.lhs) =
        reduce p (@evalInMagma _ _ (family colour left right Int) v K.rhs) :=
    (eval_reduce colour left right p K.lhs v).trans
      ((h p hp hp2 _).trans (eval_reduce colour left right p K.rhs v).symm)
  apply Prod.ext
  · exact congrArg (fun z : B × ZMod 3 => z.1) (he 3 (by decide) (by decide))
  · apply ReductionImage.int_eq_of_prime_reductions
    intro p hp hp2
    exact congrArg Prod.snd (he p hp hp2)

/-- Surjective reduction then transfers it to the potentially singular fibre. -/
theorem mod_two_of_integer {K : NatMagmaLaw}
    (h : @satisfies _ _ (family colour left right Int) K) :
    @satisfies _ _ (family colour left right (ZMod 2)) K := by
  intro v
  let w : Nat → B × Int := fun i => ((v i).1, ((v i).2.val : Int))
  have hw (i) : reduce 2 (w i) = v i := by simp [w, reduce]
  have he := congrArg (reduce 2) (h w)
  rw [eval_reduce, eval_reduce] at he
  simpa only [hw] using he

/-- A single finite algebra inherits every equation common to the images. -/
theorem bad_inherits [Finite B] {L K : NatMagmaLaw}
    (hm : ∀ p : Nat, p.Prime → 2 < p →
      InImage L .left (family colour left right (ZMod p)))
    (h : ∀ (A : Type) [Finite A] (D : Magma A), InImage L .left D →
      @satisfies _ A D K) : @satisfies _ _ (family colour left right (ZMod 2)) K := by
  apply mod_two_of_integer
  apply integer_of_odd_primes
  intro p hp hp2
  letI : Fact p.Prime := ⟨hp⟩
  exact h _ _ (hm p hp hp2)

theorem obstruction [Finite B] {L : NatMagmaLaw}
    (hm : ∀ p : Nat, p.Prime → 2 < p →
      InImage L .left (family colour left right (ZMod p)))
    (hb : ¬ IsSideQuasigroup .left (family colour left right (ZMod 2))) :
    ¬ SingleEquation .fin L .left := by
  rintro ⟨K, hK⟩
  have hh := bad_inherits colour left right hm (K := K) (by
    intro A hA D hd
    exact (hK A D hA).mpr hd)
  exact hb (characterizes_sideQuasigroup hK _ _
    (inferInstance : Finite (B × ZMod 2)) hh)

end Parastrophes.PartitionedReductionImage
