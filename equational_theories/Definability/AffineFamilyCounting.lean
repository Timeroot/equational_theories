import equational_theories.Definability.AffineCounting
import equational_theories.Definability.CloneFamilyCounting

/-! All affine coefficient triples form an injective clone family. This variant
counts the source family directly instead of listing a long array of factors. -/

namespace Magma.AffineFamily
variable {R : Type} [CommRing R]
abbrev P (R : Type) := R × R × R
def op (p : P R) (x y : R) : R := p.1 * x + p.2.1 * y + p.2.2
def comp (p q r : P R) : P R :=
  (p.1 * q.1 + p.2.1 * r.1,
   p.1 * q.2.1 + p.2.1 * r.2.1,
   p.1 * q.2.2 + p.2.1 * r.2.2 + p.2.2)
theorem op_injective : Function.Injective (op (R := R)) := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  have hc : c = f := by simpa [op] using congrFun (congrFun h 0) 0
  have ha : a = d := by simpa [op, hc] using congrFun (congrFun h 1) 0
  have hb : b = e := by simpa [op, hc] using congrFun (congrFun h 0) 1
  exact Prod.ext ha (Prod.ext hb hc)
theorem op_fst (x y : R) : op (1, 0, 0) x y = x := by simp [op]
theorem op_snd (x y : R) : op (0, 1, 0) x y = y := by simp [op]
theorem op_comp (p q r : P R) (x y : R) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := by
  simp only [op, comp]
  ring
end Magma.AffineFamily
