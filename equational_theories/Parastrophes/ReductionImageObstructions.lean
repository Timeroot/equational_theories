import equational_theories.Parastrophes.AffineImageObstructions
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Division-image obstructions from a singular reduction

An integer operation can have genuine finite division models at all odd primes,
while its reduction at 2 has a nonbijective translation. Any identity common to
the finite division models passes first to the integers and then to that bad
reduction. This rules out every defining identity, regardless of its size.
-/
namespace Parastrophes.ReductionImage
open Law FreeMagma AffineImage

theorem two_ne_zero {p : Nat} (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro hz
  have he := ZMod.natCast_eq_zero_iff 2 p
  norm_num only [Nat.cast_ofNat] at he
  exact Nat.not_dvd_of_pos_of_lt (by decide) hp (he.mp hz)

theorem int_eq_of_prime_reductions {a b : Int}
    (h : ∀ p : Nat, p.Prime → 2 < p → (a : ZMod p) = (b : ZMod p)) : a = b := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes ((b - a).natAbs + 3)
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b p).mp
    (h p hprime (by omega))
  have hz : b - a = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by
    rw [Int.natAbs_natCast]
    omega)
  omega

theorem integer_of_prime_reductions {d : Nat} (D : Magma (Fin d → Int))
    (Dn : ∀ n : Nat, Magma (Fin d → ZMod n))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    {L : NatMagmaLaw}
    (h : ∀ p : Nat, p.Prime → 2 < p → @satisfies _ _ (Dn p) L) :
    @satisfies _ _ D L := by
  have he (n : Nat) (t : FreeMagma Nat) (v : Nat → Fin d → Int) :
      reduce n (@evalInMagma _ _ D v t) =
        @evalInMagma _ _ (Dn n) (fun i => reduce n (v i)) t := by
    induction t with
    | Leaf => rfl
    | Fork a b ha hb => exact (hc n _ _).trans (congrArg₂ (Dn n).op ha hb)
  intro v
  funext i
  apply int_eq_of_prime_reductions
  intro p hp hp2
  exact congrFun ((he p L.lhs v).trans ((h p hp hp2 _).trans (he p L.rhs v).symm)) i

@[implicit_reducible] def leftZero : Magma (ZMod 2) := ⟨fun x _ => x⟩

/-- Every identity passes through a surjective projection onto left zero. -/
theorem leftZero_of_projection {V : Type} (D : Magma V)
    (project : V → ZMod 2) (sample : ZMod 2 → V)
    (hs : ∀ x, project (sample x) = x)
    (hp : ∀ x y, project (D.op x y) = project x)
    {L : NatMagmaLaw} (h : @satisfies _ _ D L) : @satisfies _ _ leftZero L := by
  have he (t : FreeMagma Nat) (v : Nat → ZMod 2) :
      project (@evalInMagma _ _ D (fun i => sample (v i)) t) =
        @evalInMagma _ _ leftZero v t := by
    induction t with
    | Leaf i => exact hs (v i)
    | Fork a b ha hb => exact (hp _ _).trans ha
  intro v
  exact (he L.lhs v).symm.trans
    ((congrArg project (h (fun i => sample (v i)))).trans (he L.rhs v))

def leftmost {A : Type} : FreeMagma A → A
  | .Leaf a => a
  | .Fork a _ => leftmost a

private theorem eval_leftZero (t : FreeMagma Nat) (v : Nat → ZMod 2) :
    @evalInMagma _ _ leftZero v t = v (leftmost t) := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => exact ha

/-- The two-element left-zero algebra detects exactly the leftmost variable. -/
theorem satisfies_leftZero_iff (L : NatMagmaLaw) :
    @satisfies _ _ leftZero L ↔ leftmost L.lhs = leftmost L.rhs := by
  constructor
  · intro h
    by_contra hn
    have he := h (fun i => if i = leftmost L.lhs then (0 : ZMod 2) else 1)
    simp only [satisfiesPhi, eval_leftZero, if_neg (Ne.symm hn)] at he
    exact (by decide : (0 : ZMod 2) ≠ 1) he
  · intro h v
    simp only [satisfiesPhi, eval_leftZero, h]

/-- Hence any common identity of the prime reductions must preserve its
leftmost variable. This obstructs arbitrary equational axiom sets, not only
single equations. -/
theorem leftmost_of_prime_reductions {d : Nat} (D : Magma (Fin d → Int))
    (Dn : ∀ n : Nat, Magma (Fin d → ZMod n))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    (project : (Fin d → Int) → ZMod 2) (sample : ZMod 2 → Fin d → Int)
    (hs : ∀ x, project (sample x) = x)
    (hp : ∀ x y, project (D.op x y) = project x)
    {L : NatMagmaLaw}
    (h : ∀ p : Nat, p.Prime → 2 < p → @satisfies _ _ (Dn p) L) :
    leftmost L.lhs = leftmost L.rhs :=
  (satisfies_leftZero_iff L).mp
    (leftZero_of_projection D project sample hs hp (integer_of_prime_reductions D Dn hc h))

/-- A surjective projection onto left zero is enough: its rows are constant,
whereas every actual left-division image has bijective rows. -/
theorem obstruction {L : NatMagmaLaw} {d : Nat}
    (D : Magma (Fin d → Int)) (Dn : ∀ n : Nat, Magma (Fin d → ZMod n))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    (hm : ∀ p : Nat, p.Prime → 2 < p → InImage L .left (Dn p))
    (project : (Fin d → Int) → ZMod 2) (sample : ZMod 2 → Fin d → Int)
    (hs : ∀ x, project (sample x) = x)
    (hp : ∀ x y, project (D.op x y) = project x) :
    ¬ SingleEquation .fin L .left := by
  rintro ⟨target, ht⟩
  have hi : @satisfies _ _ D target := integer_of_prime_reductions D Dn hc (by
    intro p hprime hp2
    letI : NeZero p := ⟨by omega⟩
    exact (ht _ (Dn p) (inferInstance : Finite (Fin d → ZMod p))).mpr (hm p hprime hp2))
  have hz := leftZero_of_projection D project sample hs hp hi
  have hQ := characterizes_sideQuasigroup ht (ZMod 2) leftZero
    (inferInstance : Finite (ZMod 2)) hz
  exact (by decide : (0 : ZMod 2) ≠ 1) ((hQ 0).1 (a₁ := 0) (a₂ := 1) rfl)

/-- The same degeneration rules out a single reverse division term across
the finite reductions. It does not rule out terms depending on the model. -/
theorem no_uniform_inverse {d : Nat}
    (D : Magma (Fin d → Int)) (Dn : ∀ n : Nat, Magma (Fin d → ZMod n))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    (project : (Fin d → Int) → ZMod 2) (sample : ZMod 2 → Fin d → Int)
    (hs : ∀ x, project (sample x) = x)
    (hp : ∀ x y, project (D.op x y) = project x) :
    ¬ ∃ t : FreeMagma (Fin 2), ∀ p : Nat, p.Prime → 2 < p →
      IsDivision .left (Dn p) (termMagma (Dn p) t) := by
  rintro ⟨t, ht⟩
  have he (n : Nat) (u : FreeMagma (Fin 2)) (v : Fin 2 → Fin d → Int) :
      reduce n (@evalInMagma _ _ D v u) =
        @evalInMagma _ _ (Dn n) (fun i => reduce n (v i)) u := by
    induction u with
    | Leaf => rfl
    | Fork a b ha hb => exact (hc n _ _).trans (congrArg₂ (Dn n).op ha hb)
  have hr (n : Nat) (x y : Fin d → Int) :
      reduce n ((termMagma D t).op x y) =
        (termMagma (Dn n) t).op (reduce n x) (reduce n y) := by
    simpa only [termMagma, apply_ite] using he n t (fun i => if i = 0 then x else y)
  have hi (x y : Fin d → Int) : D.op x ((termMagma D t).op x y) = y := by
    funext i
    apply int_eq_of_prime_reductions
    intro p hprime hp2
    have h := hc p x ((termMagma D t).op x y)
    rw [hr] at h
    exact congrFun (h.trans ((ht p hprime hp2).1 _ _)) i
  have h := congrArg project (hi (sample 0) (sample 1))
  rw [hp, hs, hs] at h
  exact (by decide : (0 : ZMod 2) ≠ 1) h

end Parastrophes.ReductionImage
