import equational_theories.Spectrum.Equation467Translations
import equational_theories.Spectrum.Equation63.OrderTen.Encoding

/-! A small, size-generic E467 encoding with a fixed squaring permutation.
All right-cancellation, fixed-point and short-cycle clauses follow from the law. -/
namespace Spectrum.E467.FixedEncoding
open Std.Sat
open E63.OrderTen.Encoding (Atom p meaning all1 sat_all1 sat_single sat_append
  exactlyOne sat_exactlyOne latin code sanitize)
variable {n : ℕ} [NeZero n]
abbrev Holds (f : Fin n → Fin n → Fin n) : Prop :=
  ∀ x y, x = f y (f x (f x (f y y)))
def diagonalClauses (d : Equiv.Perm (Fin n)) : CNF (Atom n) := all1 fun x =>
  ⟨#[[(p x x (d x),true)],
     [(p x (d x) (d.symm x),true)],
     [(p x (d (d x)) (d (d x)),true)]]⟩ ++
  (all1 fun y => if y ≠ d (d x) then ⟨#[[(p x y y,false)]]⟩ else .empty) ++
  (all1 fun y => all1 fun z => if y.val < z.val then
    ⟨#[[(p x y z,false),(p x z y,false)]]⟩ else .empty)

def triangles (d : Equiv.Perm (Fin n)) : CNF (Atom n) := all1 fun x => all1 fun y =>
  let ry := d.symm y
  all1 fun a => all1 fun b =>
  ⟨#[[(p x y a,false),(p x a b,false),(p ry b x,true)],
     [(p x y a,false),(p x a b,true),(p ry b x,false)],
     [(p x y a,true),(p x a b,false),(p ry b x,false)]]⟩


def chain (slack : ℕ) : CNF (Atom n) := all1 fun y => all1 fun z =>
  if y.val + slack < z.val then ⟨#[[(p 0 y z,false)]]⟩ else .empty

def formula (d : Equiv.Perm (Fin n)) (slack : ℕ) : CNF (Atom n) :=
  latin ++ diagonalClauses d ++ triangles d ++ chain slack
theorem model_latin (f : Fin n → Fin n → Fin n) (h : Holds f) : latin.Sat (meaning f) := by
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_append
  · apply sat_append
    · apply sat_exactlyOne
      · exact ⟨f x y, by simp [meaning]⟩
      · intro z w hz hw
        simp only [meaning, decide_eq_true_eq] at hz hw
        exact hz.symm.trans hw
    · apply sat_exactlyOne
      · obtain ⟨z,hz⟩ := Finite.surjective_of_injective (E467.left_injective f h x) y
        exact ⟨z,by simp [meaning,hz]⟩
      · intro z w hz hw
        simp only [meaning, decide_eq_true_eq] at hz hw
        exact E467.left_injective f h x (hz.trans hw.symm)
  · apply sat_exactlyOne
    · obtain ⟨z,hz⟩ := Finite.surjective_of_injective (E467.right_injective f h x) y
      exact ⟨z,by simp [meaning,hz]⟩
    · intro z w hz hw
      simp only [meaning, decide_eq_true_eq] at hz hw
      exact E467.right_injective f h x (hz.trans hw.symm)

theorem model_diagonal (d : Equiv.Perm (Fin n)) (f : Fin n → Fin n → Fin n) (h : Holds f) (hd : ∀ x, f x x = d x) :
    (diagonalClauses d).Sat (meaning f) := by
  have hroot (x : Fin n) : f x (d x) = d.symm x := by
    have hh := E467.root_square f h (d.symm x)
    change E467.root f (f _ _) = _ at hh
    rw [hd, Equiv.apply_symm_apply] at hh
    simpa only [E467.root, E467.square, hd] using hh
  have hfixed (x y : Fin n) : f x y = y ↔ y = d (d x) := by
    simpa only [E467.square, hd] using E467.translation_fixed_iff f h x y
  apply sat_all1; intro x
  apply sat_append
  · apply sat_append
    · simp [CNF.Sat, CNF.eval, CNF.Clause.eval, meaning, p, hd, hroot,
        (hfixed x (d (d x))).mpr rfl]
    · apply sat_all1; intro y
      split
      · rename_i hy
        apply sat_single
        have he : f x y ≠ y := fun he => hy ((hfixed x y).mp he)
        simp [CNF.Clause.eval, meaning, p, he]
      · exact CNF.sat_empty
  · apply sat_all1; intro y
    apply sat_all1; intro z
    split
    · rename_i hyz
      apply sat_single
      by_cases he : f x y = z
      · have he' : f x z ≠ y := by
          intro he'
          have := congrArg Fin.val (E467.no_two_cycle f h x y z he he')
          omega
        simp [CNF.Clause.eval,meaning,p,he']
      · simp [CNF.Clause.eval,meaning,p,he]
    · exact CNF.sat_empty

theorem model_triangles (d : Equiv.Perm (Fin n)) (f : Fin n → Fin n → Fin n) (h : Holds f) (hd : ∀ x, f x x = d x) :
    (triangles d).Sat (meaning f) := by
  have recover (x y : Fin n) : f (d.symm y) (f x (f x y)) = x := by
    simpa only [hd, Equiv.apply_symm_apply] using (h x (d.symm y)).symm
  apply sat_all1; intro x
  apply sat_all1; intro y
  apply sat_all1; intro a
  apply sat_all1; intro b
  have hab (ha : f x y = a) (hb : f x a = b) : f (d.symm y) b = x := by
    simpa only [ha,hb] using recover x y
  have hac (ha : f x y = a) (hc : f (d.symm y) b = x) : f x a = b := by
    apply E467.left_injective f h (d.symm y)
    simpa only [ha,hc] using recover x y
  have hbc (hb : f x a = b) (hc : f (d.symm y) b = x) : f x y = a := by
    apply E467.left_injective f h x
    apply E467.left_injective f h (d.symm y)
    simpa only [hb,hc] using recover x y
  by_cases ha : f x y = a <;> by_cases hb : f x a = b <;>
    by_cases hc : f (d.symm y) b = x <;>
    simp_all [CNF.Sat,CNF.eval,CNF.Clause.eval,meaning,p]


lemma model_chain (f : Fin n → Fin n → Fin n) (slack : ℕ)
    (hc : ∀ y, (f 0 y).val ≤ y.val + slack) : (chain slack).Sat (meaning f) := by
  apply sat_all1; intro y
  apply sat_all1; intro z
  split
  · rename_i hz
    apply sat_single
    have he : f 0 y ≠ z := by intro he; have := hc y; rw [he] at this; omega
    simp [CNF.Clause.eval,meaning,p,he]
  · exact CNF.sat_empty

theorem model_formula (d : Equiv.Perm (Fin n)) (slack : ℕ)
    (f : Fin n → Fin n → Fin n) (h : Holds f) (hd : ∀ x, f x x = d x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + slack) : (formula d slack).Sat (meaning f) := by
  simp only [formula,CNF.Sat,CNF.eval_append,Bool.and_eq_true]
  exact ⟨⟨⟨model_latin f h, model_diagonal d f h hd⟩,
    model_triangles d f h hd⟩,model_chain f slack hc⟩

def natFormula (d : Equiv.Perm (Fin n)) (slack : ℕ) : CNF ℕ :=
  sanitize ((formula d slack).relabel code)

theorem code12_injective : Function.Injective (@code 12) := by
  rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ he
  dsimp [code] at he
  have hz : z = z' := Fin.ext (by omega)
  have hy : y = y' := Fin.ext (by omega)
  have hx : x = x' := Fin.ext (by omega)
  exact Prod.ext hx (Prod.ext hy hz)

theorem impossible_of_unsat (d : Equiv.Perm (Fin 12)) (slack : ℕ)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds f) (hd : ∀ x, f x x = d x)
    (hc : ∀ y, (f 0 y).val ≤ y.val + slack) (hu : (natFormula d slack).Unsat) : False := by
  have hu' : ((formula d slack).relabel code).Unsat := by
    intro a
    cases he : (((formula d slack).relabel code).eval a) with
    | false => rfl
    | true =>
      have hs : (natFormula d slack).Sat a := by
        simp only [CNF.Sat,CNF.eval,natFormula,sanitize,Array.all_eq_true_iff_forall_mem] at he ⊢
        exact fun c hc => he c (Array.mem_filter.mp hc).1
      have hh := hu a
      rw [hs] at hh
      exact Bool.noConfusion hh
  have hraw := (CNF.unsat_relabel_iff (fun _ _ he => code12_injective he)).mp hu'
  have hh := hraw (meaning f)
  rw [model_formula d slack f h hd hc] at hh
  contradiction
end Spectrum.E467.FixedEncoding
