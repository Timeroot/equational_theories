import equational_theories.Definability.E125TranslationSeparation
import Mathlib.Tactic.LinearCombination

/-!
# Bijective unary terms need not commute in an E125 magma

The base and fibre are both `ZMod 7`. Extend `x*y=4*x+4*y+1` by a
three-entry cocycle. The cocycle condition takes only 49 small checks;
linearity in the fibre then proves E125 symbolically on all 49 elements.
Every unary term is triangular: `(x,a) ↦ (x+c,a+d(x))`, so is bijective.
Nevertheless the square and cube maps do not commute, and the square's
second iterate is not an endomorphism. These refute proposed unary-map
obstructions; they do not themselves separate two catalogue classes.
-/

namespace E125UnaryCountermodel
abbrev K := ZMod 7
abbrev G := K × K

def κ (x y : K) : K :=
  if (x=0 ∧ y=2) ∨ (x=2 ∧ y=0) then 5 else if x=2 ∧ y=2 then 1 else 0

@[reducible] def model : Magma G := ⟨fun x y =>
  (E125Translation.model.op x.1 y.1, 4*x.2+4*y.2+κ x.1 y.1)⟩

lemma cocycle (x y : K) :
    2*κ y x+4*κ (E125Translation.model.op y x) y+
      κ y (E125Translation.model.op (E125Translation.model.op y x) y)=0 := by
  revert x y
  decide

lemma equation125 : @Equation125 G model := by
  rintro ⟨x,a⟩ ⟨y,b⟩
  apply Prod.ext
  · exact E125Translation.equation125 x y
  · change a = 4*b+4*(4*(4*b+4*a+κ y x)+4*b+
      κ (E125Translation.model.op y x) y)+
      κ y (E125Translation.model.op (E125Translation.model.op y x) y)
    have hc := cocycle x y
    have h7 : (7 : K)=0 := by decide
    linear_combination -hc - (9*a+12*b+2*κ y x)*h7

/-- Every unary term acts triangularly, by a translation in each coordinate. -/
lemma unary_shape (t : FreeMagma Unit) : ∃ c : K, ∃ d : K → K,
    ∀ x a, @FreeMagma.evalInMagma Unit G model (fun _ => (x,a)) t = (x+c,a+d x) := by
  induction t with
  | Leaf _ => exact ⟨0, fun _ => 0, fun x a => by simp [FreeMagma.evalInMagma]⟩
  | Fork u v hu hv =>
    obtain ⟨c,d,hd⟩ := hu
    obtain ⟨e,f,hf⟩ := hv
    refine ⟨4*c+4*e+1, fun x => 4*d x+4*f x+κ (x+c) (x+e), fun x a => ?_⟩
    change model.op (@FreeMagma.evalInMagma Unit G model (fun _ => (x,a)) u)
      (@FreeMagma.evalInMagma Unit G model (fun _ => (x,a)) v) = _
    rw [hd,hf]
    change (4*(x+c)+4*(x+e)+1, 4*(a+d x)+4*(a+f x)+κ (x+c) (x+e)) = _
    apply Prod.ext <;> dsimp only <;> ring_nf <;>
      rw [show (8 : K)=1 by decide] <;> simp

lemma unary_bijective (t : FreeMagma Unit) :
    Function.Bijective (fun x : G => @FreeMagma.evalInMagma Unit G model (fun _ => x) t) := by
  obtain ⟨c,d,hd⟩ := unary_shape t
  constructor
  · rintro ⟨x,a⟩ ⟨y,b⟩ h
    dsimp only at h
    rw [hd,hd] at h
    have hx : x=y := add_right_cancel (congrArg Prod.fst h)
    subst y
    have ha : a=b := add_right_cancel (congrArg Prod.snd h)
    subst b
    rfl
  · rintro ⟨x,a⟩
    refine ⟨(x-c,a-d (x-c)), ?_⟩
    dsimp only
    rw [hd]
    simp

def square (x : G) := model.op x x
def cube (x : G) := model.op x (square x)

lemma square_cube_ne : square (cube (1,0)) ≠ cube (square (1,0)) := by decide

lemma square_twice_not_endo : ¬ model.IsEndo (square ∘ square) := by
  intro h
  have hh := h (0,0) (1,0)
  exact (by decide : square (square (model.op (0,0) (1,0))) ≠
    model.op (square (square (0,0))) (square (square (1,0)))) hh

end E125UnaryCountermodel

spectrum_assert E125UnaryCountermodel.equation125 complete
spectrum_assert E125UnaryCountermodel.unary_bijective complete
spectrum_assert E125UnaryCountermodel.square_cube_ne complete
spectrum_assert E125UnaryCountermodel.square_twice_not_endo complete
