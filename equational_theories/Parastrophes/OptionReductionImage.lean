import equational_theories.Parastrophes.ReductionImageObstructions
import equational_theories.Parastrophes.FoldedExtensions

/-!
# Singular reductions of right-zero extensions

The extra row in a right-zero extension need not stay invertible under reduction,
even when all the old rows do. Identities of the odd-prime division models pass
to the integral model and then to characteristic two. Thus a single collision
there obstructs every equational characterization of the finite division image.
-/
namespace Parastrophes.OptionReductionImage
open Law FreeMagma

abbrev Carrier (d : Nat) (R : Type) := Option (Fin d → R)

def reduce {d : Nat} (n : Nat) : Carrier d Int → Carrier d (ZMod n) :=
  Option.map (AffineImage.reduce n)

theorem separate {d : Nat} {x y : Carrier d Int}
    (h : ∀ p : Nat, p.Prime → 2 < p → reduce p x = reduce p y) : x = y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some y => have := h 3 (by decide) (by decide); cases this
  | some x => cases y with
    | none => have := h 3 (by decide) (by decide); cases this
    | some y =>
      congr 1
      funext i
      apply ReductionImage.int_eq_of_prime_reductions
      intro p hp hp2
      exact congrFun (Option.some.inj (h p hp hp2)) i

theorem eval_reduce {d : Nat} (D : Magma (Carrier d Int))
    (Dn : ∀ n : Nat, Magma (Carrier d (ZMod n)))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    {α : Type} (n : Nat) (t : FreeMagma α) (v : α → Carrier d Int) :
    reduce n (@evalInMagma _ _ D v t) =
      @evalInMagma _ _ (Dn n) (fun i => reduce n (v i)) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => exact (hc n _ _).trans (congrArg₂ (Dn n).op ha hb)

theorem integer_of_prime_reductions {d : Nat} (D : Magma (Carrier d Int))
    (Dn : ∀ n : Nat, Magma (Carrier d (ZMod n)))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    {L : NatMagmaLaw}
    (h : ∀ p : Nat, p.Prime → 2 < p → @satisfies _ _ (Dn p) L) :
    @satisfies _ _ D L := by
  intro v
  apply separate
  intro p hp hp2
  exact (eval_reduce D Dn hc p L.lhs v).trans
    ((h p hp hp2 _).trans (eval_reduce D Dn hc p L.rhs v).symm)

private def liftTwo {d : Nat} : Carrier d (ZMod 2) → Carrier d Int :=
  Option.map (fun x i => (x i).val)

private theorem reduce_liftTwo {d : Nat} (x : Carrier d (ZMod 2)) :
    reduce 2 (liftTwo x) = x := by
  cases x with
  | none => rfl
  | some x =>
    apply congrArg some
    funext i
    simp [AffineImage.reduce]

/-- Any common identity of the odd-prime models also holds in the bad reduction.
This statement can be applied separately to every member of an axiom set. -/
theorem two_of_prime_reductions {d : Nat} (D : Magma (Carrier d Int))
    (Dn : ∀ n : Nat, Magma (Carrier d (ZMod n)))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    {L : NatMagmaLaw}
    (h : ∀ p : Nat, p.Prime → 2 < p → @satisfies _ _ (Dn p) L) :
    @satisfies _ _ (Dn 2) L := by
  have hi := integer_of_prime_reductions D Dn hc h
  intro v
  have he := congrArg (reduce 2) (hi (fun i => liftTwo (v i)))
  simpa only [satisfiesPhi, eval_reduce D Dn hc, reduce_liftTwo] using he

theorem obstruction {L : NatMagmaLaw} {d : Nat}
    (D : Magma (Carrier d Int)) (Dn : ∀ n : Nat, Magma (Carrier d (ZMod n)))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    (hm : ∀ p : Nat, p.Prime → 2 < p → InImage L .left (Dn p))
    (hbad : ¬ IsSideQuasigroup .left (Dn 2)) :
    ¬ SingleEquation .fin L .left := by
  rintro ⟨target, ht⟩
  apply hbad
  apply characterizes_sideQuasigroup ht _ (Dn 2) (inferInstance : Finite (Carrier d (ZMod 2)))
  apply two_of_prime_reductions D Dn hc
  intro p hprime hp2
  letI : NeZero p := ⟨by omega⟩
  exact (ht _ (Dn p) (inferInstance : Finite (Carrier d (ZMod p)))).mpr (hm p hprime hp2)

/-- The same singular reduction prevents one term from recovering multiplication
from division across the odd-prime family. Individual finite models still have
inverse terms; this conclusion is specifically about uniformity. -/
theorem no_uniform_inverse {d : Nat}
    (D : Magma (Carrier d Int)) (Dn : ∀ n : Nat, Magma (Carrier d (ZMod n)))
    (hc : ∀ n x y, reduce n (D.op x y) = (Dn n).op (reduce n x) (reduce n y))
    (hbad : ¬ IsSideQuasigroup .left (Dn 2)) :
    ¬ ∃ t : FreeMagma (Fin 2), ∀ p : Nat, p.Prime → 2 < p →
      IsDivision .left (Dn p) (termMagma (Dn p) t) := by
  rintro ⟨t, ht⟩
  have hr (n : Nat) (x y : Carrier d Int) :
      reduce n ((termMagma D t).op x y) =
        (termMagma (Dn n) t).op (reduce n x) (reduce n y) := by
    simpa only [termMagma, apply_ite] using
      eval_reduce D Dn hc n t (fun i => if i = 0 then x else y)
  have hi (x y : Carrier d Int) : (termMagma D t).op x (D.op x y) = y := by
    apply separate
    intro p hp hp2
    have he := hr p x (D.op x y)
    rw [hc] at he
    exact he.trans ((ht p hp hp2).2 _ _)
  have htwo (x y : Carrier d (ZMod 2)) :
      (termMagma (Dn 2) t).op x ((Dn 2).op x y) = y := by
    have he := congrArg (reduce 2) (hi (liftTwo x) (liftTwo y))
    simpa only [hr, hc, reduce_liftTwo] using he
  apply hbad
  intro x
  have hinj : Function.Injective ((Dn 2).op x) := by
    intro a b hab
    exact (htwo x a).symm.trans
      ((congrArg ((termMagma (Dn 2) t).op x) hab).trans (htwo x b))
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

/-- Left division extends over an adjoined right zero by inverting its new row. -/
theorem extension_division {G : Type*} (op div : G → G → G) (f h : G → G)
    (hd : IsDivision .left ⟨op⟩ ⟨div⟩)
    (hfh : ∀ x, f (h x) = x) (hhf : ∀ x, h (f x) = x) :
    IsDivision .left (FoldedExtensions.extension op f) (FoldedExtensions.extension div h) := by
  constructor <;> rintro (_ | x) (_ | y)
  all_goals first
    | rfl
    | exact congrArg some (hfh y)
    | exact congrArg some (hhf y)
    | exact congrArg some (hd.1 x y)
    | exact congrArg some (hd.2 x y)

end Parastrophes.OptionReductionImage
