import equational_theories.Spectrum.Equation1279.Encoding

/-! Once the diagonal is fixed, the middle term `(x*x)*y` is simply `d(x)*y`.
Use table atoms directly: no auxiliary operation or auxiliary atoms are needed. -/
namespace Spectrum.E1279.DirectEncoding
open Std.Sat SmallOrders
open SmallOrders.Encoding (Atom p meaning code)
open E63.OrderTen.Encoding (all1 sat_all1 sat_single sat_append sanitize)
variable {n : ℕ} [NeZero n]

def identities (d : Fin n → Fin n) : CNF (Atom n) := all1 fun x => all1 fun y =>
  all1 fun a => all1 fun b =>
  ⟨#[[(p (d x) y a,false),(p a y b,false),(p y b x,true)],
     [(p (d x) y a,false),(p a y b,true),(p y b x,false)],
     [(p (d x) y a,true),(p a y b,false),(p y b x,false)]]⟩

def formula (d : Fin n → Fin n) (k : ℕ) : CNF (Atom n) :=
  SmallOrders.Encoding.latin .e1279 ++ identities d ++ Encoding.units d ++ Encoding.rowBound k

def natFormula (d : Fin n → Fin n) (k : ℕ) : CNF ℕ := Encoding.toNat (formula d k)

omit [NeZero n] in
lemma model_identities (d : Fin n → Fin n) (f : Fin n → Fin n → Fin n)
    (h : Holds .e1279 f) (hD : ∀ x, f x x = d x) :
    (identities d).Sat (meaning .e1279 f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_all1; intro b
  have he : f y (f (f (d x) y) y) = x := by simpa only [Holds,middle,first,inner,last,hD] using h x y
  have forward (ha : f (d x) y = a) (hb : f a y = b) : f y b = x := by rwa [ha,hb] at he
  have reverse (ha : f (d x) y = a) (hc : f y b = x) : f a y = b := by
    apply (left_bijective h y).1
    simpa only [ha,hc] using he
  have recover (hb : f a y = b) (hc : f y b = x) : f (d x) y = a := by
    apply (right_bijective h rfl y).1
    apply (left_bijective h y).1
    simpa only [hb,hc] using he
  by_cases ha : f (d x) y = a <;> by_cases hb : f a y = b <;> by_cases hc : f y b = x <;>
    simp_all [CNF.Sat,CNF.eval,CNF.Clause.eval,meaning,p]

lemma model_formula (d : Fin n → Fin n) (k : ℕ)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1279 f)
    (hD : ∀ x, f x x = d x) (hc : ∀ y, (f 0 y).val ≤ y.val + k) :
    (formula d k).Sat (meaning .e1279 f) := by
  apply sat_append
  · apply sat_append
    · apply sat_append
      · exact SmallOrders.Encoding.model_latin .e1279 f h
      · exact model_identities d f h hD
    · apply sat_all1; intro x
      apply sat_single
      simp [CNF.Clause.eval,meaning,p,hD]
  · apply sat_all1; intro y
    apply sat_all1; intro z
    split
    · rename_i hz
      apply sat_single
      have he : f 0 y ≠ z := by intro he; have := hc y; have := congrArg Fin.val he; omega
      simp [CNF.Clause.eval,meaning,p,he]
    · exact CNF.sat_empty

theorem no_operation (d : Fin n → Fin n) (k : ℕ)
    (hn : (natFormula d k).Unsat) (f : Fin n → Fin n → Fin n) (h : Holds .e1279 f)
    (hD : ∀ x, f x x = d x) (hc : ∀ y, (f 0 y).val ≤ y.val + k) : False := by
  have hh := E1110.SquareEncoding.unsat_of_toNat_unsat hn (meaning .e1279 f)
  rw [model_formula d k f h hD hc] at hh
  contradiction
end Spectrum.E1279.DirectEncoding
