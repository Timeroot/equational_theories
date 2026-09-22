import equational_theories.Spectrum.QuasigroupBounds
import equational_theories.Spectrum.TripleSelection
import Mathlib.Data.ZMod.Basic

/-! Cyclic constructions for the remaining orders of E115. -/
namespace Spectrum.Cyclic115
open Classical

structure Data (A : Type*) [AddCommGroup A] where
  next : A → A
  shift : A
  point : A
  shift_ne_zero : shift ≠ 0
  next_zero : next 0 = shift
  period : ∀ x, next (next (next x)) = x
  sum : ∀ x, x + next x + next (next x) = -shift
  fixed : ∀ x, next x = x ↔ x = point

variable {A Q : Type*} [AddCommGroup A]

theorem Data.selected [Fintype A] (D : Data A) {r : ℕ}
    (hm : Fintype.card A % 3 = 1) (hr : r % 3 = 1) (hlt : r < Fintype.card A) :
    ∃ s : Finset A, s.card = r ∧ 0 ∉ s ∧ ∀ x, D.next x ∈ s ↔ x ∈ s := by
  classical
  have hp : D.next D.point = D.point := (D.fixed _).mpr rfl
  have hinj : Function.Injective D.next := fun x y h => by
    simpa only [D.period] using congrArg (fun z => D.next (D.next z)) h
  have hp0 : D.point ≠ 0 := by
    intro he
    have hh := hp
    rw [he, D.next_zero] at hh
    exact D.shift_ne_zero hh
  let o := TripleSelection.orbit D.next 0
  have hoc : o.card = 3 := TripleSelection.orbit_card D.next D.period
    (by simpa only [D.next_zero] using D.shift_ne_zero)
  have hpo : D.point ∉ o := by
    simp only [o, TripleSelection.orbit, Finset.mem_insert, Finset.mem_singleton]
    rintro (he | he | he)
    · exact hp0 he
    · exact hp0 (hinj (hp.trans he))
    · exact hp0 (hinj (hinj (by rw [hp, hp]; exact he)))
  let available := Finset.univ \ insert D.point o
  have ha : available.card = Fintype.card A - 4 := by
    simp [available, Finset.card_sdiff_of_subset (Finset.subset_univ _), hpo, hoc]
  have hac : ∀ x ∈ available, D.next x ∈ available := by
    intro x hx
    have hn := (Finset.mem_sdiff.mp hx).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro he
    rcases Finset.mem_insert.mp he with he | he
    · exact hn (Finset.mem_insert.mpr (Or.inl (hinj (he.trans hp.symm))))
    · exact hn (Finset.mem_insert_of_mem ((TripleSelection.orbit_mem D.next D.period 0 x).mp he))
  have haf : ∀ x ∈ available, D.next x ≠ x := by
    intro x hx he
    have he' := (D.fixed x).mp he
    subst x
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_self _ _)
  obtain ⟨t,ht,htc,htg⟩ := TripleSelection.select D.next D.period (r/3) available hac haf
    (by rw [ha]; omega)
  have hpt : D.point ∉ t := fun h =>
    (Finset.mem_sdiff.mp (ht h)).2 (Finset.mem_insert_self _ _)
  refine ⟨insert D.point t, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hpt, htc]
    omega
  · intro he
    rcases Finset.mem_insert.mp he with he | he
    · exact hp0 he.symm
    · exact (Finset.mem_sdiff.mp (ht he)).2 (by simp [o, TripleSelection.orbit])
  · have hcl : ∀ x ∈ insert D.point t, D.next x ∈ insert D.point t := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp [hp]
      · exact Finset.mem_insert_of_mem (htg x hx)
    intro x
    exact ⟨fun h => by simpa only [D.period] using hcl _ (hcl _ h), hcl x⟩

def Data.timesSeven (D : Data A) : Data (A × ZMod 7) where
  next x := (D.next x.1, 2 * x.2)
  shift := (D.shift, 0)
  point := (D.point, 0)
  shift_ne_zero h := D.shift_ne_zero (congrArg Prod.fst h)
  next_zero := Prod.ext D.next_zero (by simp)
  period x := by
    apply Prod.ext (D.period x.1)
    change (2 : ZMod 7) * (2 * (2 * x.2)) = x.2
    ring_nf
    rw [show (8 : ZMod 7) = 1 by decide, mul_one]
  sum x := by
    apply Prod.ext (D.sum x.1)
    change x.2 + (2 : ZMod 7) * x.2 + 2 * (2 * x.2) = -0
    ring_nf
    rw [show (7 : ZMod 7) = 0 by decide, mul_zero]
  fixed x := by
    rcases x with ⟨x,y⟩
    change (D.next x, (2 : ZMod 7) * y) = (x,y) ↔ (x,y) = (D.point,0)
    rw [Prod.mk.injEq, Prod.mk.injEq, D.fixed]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1, by linear_combination h2⟩
    · rintro ⟨h1,h2⟩
      exact ⟨h1, by simp [h2]⟩

noncomputable def op (D : Data A) (s : Finset A) (f : Q ≃ {x // x ∈ s})
    (M : Mendelsohn Q) : A ⊕ Q → A ⊕ Q → A ⊕ Q
  | .inl x, .inl y =>
    if h : y - x ∈ s then .inr (f.symm ⟨y-x,h⟩) else .inl (y + D.next (y-x))
  | .inl x, .inr y => .inl (x - D.shift - (f y).val)
  | .inr x, .inl y => .inl (y + (f x).val)
  | .inr x, .inr y => .inr (M.op x y)

theorem law (D : Data A) (s : Finset A) (f : Q ≃ {x // x ∈ s})
    (M : Mendelsohn Q) (hz : 0 ∉ s) (hc : ∀ x, D.next x ∈ s ↔ x ∈ s) :
    @Equation115 (A ⊕ Q) ⟨op D s f M⟩ := by
  have diag (x : A) : op D s f M (.inl x) (.inl x) = .inl (x + D.shift) := by
    simp [op, hz, D.next_zero]
  have diag' (x : Q) : op D s f M (.inr x) (.inr x) = .inr x := by
    simp [op, M.idem]
  intro x y
  change x = op D s f M y (op D s f M (op D s f M x x) y)
  cases x with
  | inl x =>
    rw [diag]
    cases y with
    | inr y =>
      simp only [op]
      congr 1
      abel
    | inl y =>
      by_cases hd : y - (x + D.shift) ∈ s
      · simp only [op, dif_pos hd, Equiv.apply_symm_apply]
        congr 1
        abel
      · have hgd : D.next (y - (x + D.shift)) ∉ s := fun h => hd ((hc _).mp h)
        simp only [op, dif_neg hd, add_sub_cancel_left, dif_neg hgd]
        congr 1
        have hs := D.sum (y - (x + D.shift))
        have hs' : D.next (y - (x + D.shift)) + D.next (D.next (y - (x + D.shift))) =
            -D.shift - (y - (x + D.shift)) := by
          apply eq_sub_iff_add_eq.mpr
          simpa only [add_assoc, add_comm, add_left_comm] using hs
        rw [add_assoc, hs']
        abel
  | inr x =>
    rw [diag']
    cases y with
    | inr y => simp [op, M.semi]
    | inl y =>
      simp only [op, add_sub_cancel_left]
      rw [dif_pos (f x).property]
      simp


def seed7 : Data (ZMod 7) where
  next x := ![1, 5, 2, 4, 6, 0, 3] x
  shift := 1
  point := 2
  shift_ne_zero := by decide
  next_zero := rfl
  period := by decide
  sum := by decide
  fixed := by decide

def seed13 : Data (ZMod 13) where
  next x := ![1, 11, 3, 7, 4, 8, 9, 2, 12, 10, 6, 0, 5] x
  shift := 1
  point := 4
  shift_ne_zero := by decide
  next_zero := rfl
  period := by decide
  sum := by decide
  fixed := by decide

def seed25 : Data (ZMod 25) where
  next x := ![1, 23, 3, 19, 5, 15, 7, 11, 8, 16, 18, 6, 17, 14, 22, 4, 24, 20, 21, 2, 12, 10, 13, 0, 9] x
  shift := 1
  point := 8
  shift_ne_zero := by decide
  next_zero := rfl
  period := by decide
  sum := by decide
  fixed := by decide


theorem exists_data_size (b : ℕ) (hb : b ∈ ({7,13,25} : Finset ℕ)) (k : ℕ) :
    ∃ (A : Type) (a : AddCommGroup A) (f : Fintype A),
      Nonempty (@Data A a) ∧ @Fintype.card A f = b * 7^k := by
  induction k with
  | zero =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · exact ⟨ZMod 7, inferInstance, inferInstance, ⟨seed7⟩, by simp⟩
    · exact ⟨ZMod 13, inferInstance, inferInstance, ⟨seed13⟩, by simp⟩
    · exact ⟨ZMod 25, inferInstance, inferInstance, ⟨seed25⟩, by simp⟩
  | succ k ih =>
    obtain ⟨A,a,f,⟨D⟩,hc⟩ := ih
    letI := a
    letI := f
    exact ⟨A × ZMod 7, inferInstance, inferInstance, ⟨D.timesSeven⟩,
      by simp [Fintype.card_prod, hc, pow_succ, Nat.mul_assoc]⟩


theorem core_size {n : ℕ} (hn : 8 ≤ n) :
    ∃ b ∈ ({7,13,25} : Finset ℕ), ∃ k : ℕ, b * 7^k < n ∧ n < 2 * (b * 7^k) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h50 : n < 50
    · by_cases h14 : n < 14
      · exact ⟨7, by simp, 0, by norm_num; omega, by norm_num; omega⟩
      · by_cases h26 : n < 26
        · exact ⟨13, by simp, 0, by norm_num; omega, by norm_num; omega⟩
        · exact ⟨25, by simp, 0, by norm_num; omega, by norm_num; omega⟩
    · obtain ⟨b,hb,k,hlo,hhi⟩ := ih ((n+6)/7) (by omega) (by omega)
      refine ⟨b,hb,k+1,?_,?_⟩ <;> rw [pow_succ]
      · have h' : 7 * (b * 7^k) < n := by omega
        nlinarith
      · have h' : n < 7 * (2 * (b * 7^k)) := by omega
        nlinarith

end Spectrum.Cyclic115

namespace Spectrum
open Law Law.MagmaLaw

theorem models_115 {n : ℕ} (h : n ∈ positiveExcept {2,6}) : Law115.HasModel n := by
  have hn : 0 < n ∧ n ≠ 2 ∧ n ≠ 6 := by simpa [positiveExcept] using h
  by_cases hr : n % 3 = 2
  · by_cases h5 : n = 5
    · subst n; exact model_115_5
    obtain ⟨b,hb,k,hlo,hhi⟩ := Cyclic115.core_size (show 8 ≤ n by omega)
    obtain ⟨A,a,f,⟨D⟩,hm⟩ := Cyclic115.exists_data_size b hb k
    letI := a
    letI := f
    have hmod : Fintype.card A % 3 = 1 := by
      rw [hm, Nat.mul_mod, Nat.pow_mod]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl <;> norm_num
    let r := n - Fintype.card A
    have hrmod : r % 3 = 1 := by dsimp [r]; omega
    have hrlt : r < Fintype.card A := by dsimp [r]; omega
    obtain ⟨s,hsc,hs0,hsg⟩ := D.selected hmod hrmod hrlt
    have hr66 : r ∈ residues 3 {0,1} {6} := by
      simp only [residues, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨by omega, Or.inr hrmod, by omega⟩
    obtain ⟨N,hN⟩ := models_66 hr66
    let M := @Mendelsohn.ofEquation66 (Fin r) N ((@Law66.models_iff _ N).mp hN)
    let e : Fin r ≃ {x // x ∈ s} := Fintype.equivOfCardEq (by simp [hsc])
    exact hasModel_of_card ⟨Cyclic115.op D s e M⟩
      ((@Law115.models_iff _ ⟨Cyclic115.op D s e M⟩).mpr (Cyclic115.law D s e M hs0 hsg))
      (by simp only [Fintype.card_sum, Fintype.card_fin]; dsimp [r]; omega)
  · exact (mendelsohn_115 (show n ∈ residues 3 {0,1} {6} from
      ⟨hn.1, by simp; omega, by simpa using hn.2.2⟩)).2

end Spectrum
