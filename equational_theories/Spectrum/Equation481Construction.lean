import equational_theories.Spectrum.QuasigroupBounds
import equational_theories.Spectrum.TripleSelection
import Mathlib.Data.ZMod.Basic
import equational_theories.Spectrum.Generated.NoteWitnesses

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-! Partial cyclic constructions for E481. -/
namespace Spectrum.Cyclic481
open Classical

structure Data (A : Type*) [AddCommGroup A] where
  next : A → A
  shift : A
  point : A
  good : Set A
  zero_notMem : 0 ∉ good
  point_mem : point ∈ good
  period : ∀ x, next (next (next x)) = x
  closed : ∀ x, next x ∈ good ↔ x ∈ good
  sum : ∀ x ∈ good, x + next x + next (next x) = shift + shift
  fixed : ∀ x ∈ good, next x = x ↔ x = point

variable {A Q : Type*} [AddCommGroup A]

theorem Data.selected [Fintype A] (D : Data A) {t : ℕ}
    (ht : t % 3 = 1) (hlt : t ≤ Nat.card D.good) :
    ∃ R : Finset A, R.card = t ∧ (∀ x ∈ R, x ∈ D.good) ∧
      ∀ x, D.next x ∈ R ↔ x ∈ R := by
  classical
  have hp : D.next D.point = D.point := (D.fixed _ D.point_mem).mpr rfl
  have hinj : Function.Injective D.next := fun x y h => by
    simpa only [D.period] using congrArg (fun z => D.next (D.next z)) h
  let available := D.good.toFinset.erase D.point
  have ha : available.card = Nat.card D.good - 1 := by
    simp [available, D.point_mem, Set.toFinset_card, Nat.card_eq_fintype_card]
  have hac : ∀ x ∈ available, D.next x ∈ available := by
    intro x hx
    obtain ⟨hne,hg⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_erase.mpr ⟨fun he => hne (hinj (he.trans hp.symm)),
      Set.mem_toFinset.mpr ((D.closed x).mpr (Set.mem_toFinset.mp hg))⟩
  have haf : ∀ x ∈ available, D.next x ≠ x := by
    intro x hx he
    obtain ⟨hne,hg⟩ := Finset.mem_erase.mp hx
    exact hne ((D.fixed x (Set.mem_toFinset.mp hg)).mp he)
  obtain ⟨u,hu,huc,hug⟩ := TripleSelection.select D.next D.period (t/3) available hac haf
    (by rw [ha]; omega)
  have hpu : D.point ∉ u := fun h => (Finset.mem_erase.mp (hu h)).1 rfl
  refine ⟨insert D.point u, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hpu, huc]; omega
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact D.point_mem
    · exact Set.mem_toFinset.mp (Finset.mem_erase.mp (hu hx)).2
  · have hcl : ∀ x ∈ insert D.point u, D.next x ∈ insert D.point u := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp [hp]
      · exact Finset.mem_insert_of_mem (hug x hx)
    intro x
    exact ⟨fun h => by simpa only [D.period] using hcl _ (hcl _ h), hcl x⟩

def Data.timesSeven (D : Data A) : Data (A × ZMod 7) where
  next x := (D.next x.1, 2 * x.2)
  shift := (D.shift, 0)
  point := (D.point, 0)
  good := {x | x.1 ∈ D.good}
  zero_notMem := D.zero_notMem
  point_mem := D.point_mem
  period x := by
    apply Prod.ext (D.period x.1)
    change (2 : ZMod 7) * (2 * (2 * x.2)) = x.2
    ring_nf
    rw [show (8 : ZMod 7) = 1 by decide, mul_one]
  closed x := D.closed x.1
  sum x hx := by
    apply Prod.ext (D.sum x.1 hx)
    change x.2 + (2 : ZMod 7) * x.2 + 2 * (2 * x.2) = 0+0
    ring_nf
    rw [show (7 : ZMod 7) = 0 by decide, mul_zero]
  fixed x hx := by
    rcases x with ⟨x,y⟩
    change (D.next x, (2 : ZMod 7) * y) = (x,y) ↔ (x,y) = (D.point,0)
    rw [Prod.mk.injEq, Prod.mk.injEq, D.fixed x hx]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1, by linear_combination h2⟩
    · rintro ⟨h1,h2⟩
      exact ⟨h1, by simp [h2]⟩

theorem Data.timesSeven_card (D : Data A) :
    Nat.card D.timesSeven.good = Nat.card D.good * 7 := by
  let e : D.timesSeven.good ≃ D.good × ZMod 7 :=
    { toFun x := (⟨x.val.1, x.property⟩, x.val.2)
      invFun x := ⟨(x.1.val, x.2), x.1.property⟩ }
  rw [Nat.card_congr e, Nat.card_prod]
  simp

noncomputable def op (g : A → A) (c : A) (s : Finset A)
    (f : Q ≃ {x // x ∈ s}) (M : Mendelsohn Q) :
    A ⊕ Option Q → A ⊕ Option Q → A ⊕ Option Q
  | .inl x, .inl y =>
    if y-x = 0 then .inr none
    else if h : y-x ∈ s then .inr (some (f.symm ⟨y-x,h⟩))
    else .inl (y + g (y-x) - c)
  | .inl x, .inr none => .inl (x+c)
  | .inr none, .inl y => .inl (y-c)
  | .inl x, .inr (some y) => .inl (x+c-(f y).val)
  | .inr (some x), .inl y => .inl (y-c+(f x).val)
  | .inr x, .inr y => .inr (M.adjoin.op x y)

theorem law (g : A → A) (c : A) (s : Finset A)
    (f : Q ≃ {x // x ∈ s}) (M : Mendelsohn Q) (hz : 0 ∉ s)
    (hc : ∀ x, x ≠ 0 → x ∉ s → g x ≠ 0 ∧ g x ∉ s)
    (hs : ∀ x, x ≠ 0 → x ∉ s → x + g x + g (g x) = c+c) :
    @Equation481 (A ⊕ Option Q) ⟨op g c s f M⟩ := by
  have diag (x : A ⊕ Option Q) : op g c s f M x x = .inr none := by
    cases x with
    | inl x => simp [op]
    | inr x => simp only [op, M.adjoin.square]; rfl
  intro x y z
  change x = op g c s f M y (op g c s f M x (op g c s f M y (op g c s f M z z)))
  rw [diag]
  cases x with
  | inl x =>
    cases y with
    | inr y =>
      cases y <;> simp only [op] <;> congr 1 <;> abel
    | inl y =>
      by_cases hd0 : y+c-x = 0
      · simp only [op, if_pos hd0]
        congr 1
        exact (sub_eq_zero.mp hd0).symm
      · by_cases hd : y+c-x ∈ s
        · simp only [op, if_neg hd0, dif_pos hd, Equiv.apply_symm_apply]
          congr 1
          abel
        · obtain ⟨hg0,hgs⟩ := hc _ hd0 hd
          have hd' : y + c + g (y+c-x) - c - y = g (y+c-x) := by abel
          simp only [op, if_neg hd0, dif_neg hd, hd', if_neg hg0, dif_neg hgs]
          congr 1
          have hh := hs _ hd0 hd
          have he : g (y+c-x) + g (g (y+c-x)) = c+c-(y+c-x) := by
            apply eq_sub_iff_add_eq.mpr
            simpa only [add_assoc, add_comm, add_left_comm] using hh
          calc
            x = y + (g (y+c-x) + g (g (y+c-x))) - c := by rw [he]; abel
            _ = _ := by abel
  | inr x =>
    cases y with
    | inr y =>
      simp only [op]
      change Sum.inr x = Sum.inr (M.adjoin.op y (M.adjoin.op x (M.adjoin.op y M.adjoin.unit)))
      rw [M.adjoin.right_unit, M.adjoin.semi]
    | inl y =>
      cases x with
      | none => simp [op]
      | some x =>
        have hf0 : (f x).val ≠ 0 := fun he => hz (he ▸ (f x).property)
        have he : y+c-c+(f x).val-y = (f x).val := by abel
        simp only [op, he, if_neg hf0, dif_pos (f x).property]
        simp


theorem Data.model [Fintype A] (D : Data A) (n : ℕ)
    (hn : Fintype.card A+1 < n) (hhi : n < 2*Fintype.card A)
    (hsize : 2*Fintype.card A-n ≤ Nat.card D.good)
    (hm : Fintype.card A % 3 = 2) (hn3 : n % 3 = 0)
    (hr6 : n-Fintype.card A-1 ≠ 6) : Law481.HasModel n := by
  classical
  let t := 2*Fintype.card A-n
  have ht : t % 3 = 1 := by dsimp [t]; omega
  obtain ⟨R,hRt,hRg,hR⟩ := D.selected ht hsize
  have hR0 : 0 ∉ R := fun h => D.zero_notMem (hRg _ h)
  let s := Finset.univ \ insert 0 R
  have hsc : s.card = n-Fintype.card A-1 := by
    simp only [s, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Finset.card_insert_of_notMem hR0, hRt]
    dsimp [t]
    omega
  have hs0 : 0 ∉ s := by simp [s]
  have hmem (x : A) : x ∈ s ↔ x ≠ 0 ∧ x ∉ R := by simp [s]
  have hxR (x : A) (hx0 : x ≠ 0) (hxs : x ∉ s) : x ∈ R := by
    by_contra h
    exact hxs ((hmem x).mpr ⟨hx0,h⟩)
  have hclosed (x : A) (hx0 : x ≠ 0) (hxs : x ∉ s) :
      D.next x ≠ 0 ∧ D.next x ∉ s := by
    have hgR := (hR x).mpr (hxR x hx0 hxs)
    exact ⟨fun he => hR0 (he ▸ hgR), fun he => ((hmem _).mp he).2 hgR⟩
  have hsum (x : A) (hx0 : x ≠ 0) (hxs : x ∉ s) :
      x+D.next x+D.next (D.next x) = D.shift+D.shift :=
    D.sum x (hRg x (hxR x hx0 hxs))
  let r := n-Fintype.card A-1
  have hrmod : r % 3 = 0 := by dsimp [r]; omega
  have hrpos : 0 < r := by dsimp [r]; omega
  have hr66 : r ∈ residues 3 {0,1} {6} := by
    simp only [residues, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hrpos, Or.inl hrmod, hr6⟩
  obtain ⟨N,hN⟩ := models_66 hr66
  let M := @Mendelsohn.ofEquation66 (Fin r) N ((@Law66.models_iff _ N).mp hN)
  let e : Fin r ≃ {x // x ∈ s} := Fintype.equivOfCardEq (by simp [hsc, r])
  exact Law.MagmaLaw.hasModel_of_card ⟨op D.next D.shift s e M⟩
    ((@Law481.models_iff _ ⟨op D.next D.shift s e M⟩).mpr
      (law D.next D.shift s e M hs0 hclosed hsum))
    (by simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_fin]; dsimp [r]; omega)


def seed11 : Data (ZMod 11) where
  next x := ![0, 1, 4, 3, 7, 9, 6, 2, 8, 10, 5] x
  shift := 1
  point := 8
  good := {x | x ∉ ({0,1,3,6} : Finset (ZMod 11))}
  zero_notMem := by decide
  point_mem := by decide
  period := by decide
  closed := by decide
  sum := by decide
  fixed := by decide

def seed17 : Data (ZMod 17) where
  next x := ![0, 1, 7, 5, 4, 11, 14, 10, 13, 9, 2, 3, 12, 15, 16, 8, 6] x
  shift := 1
  point := 12
  good := {x | x ∉ ({0,1,4,9} : Finset (ZMod 17))}
  zero_notMem := by decide
  point_mem := by decide
  period := by decide
  closed := by decide
  sum := by decide
  fixed := by decide

def seed29 : Data (ZMod 29) where
  next x := ![0, 11, 6, 13, 5, 22, 23, 10, 24, 25, 14, 19, 21, 15, 7, 3, 16, 17, 18, 1, 20, 27, 4, 2, 28, 26, 9, 12, 8] x
  shift := 1
  point := 20
  good := {x | x ∉ ({0,16,17,18} : Finset (ZMod 29))}
  zero_notMem := by decide
  point_mem := by decide
  period := by decide
  closed := by decide
  sum := by decide
  fixed := by decide

def seed53 : Data (ZMod 53) where
  next x := ![0, 7, 9, 10, 8, 17, 50, 47, 43, 44, 42, 46, 16, 19, 20, 18, 27, 33, 22, 23, 21, 14, 15, 13, 35, 25, 37, 12, 39, 31, 38, 48, 32, 5, 34, 49, 36, 45, 40, 41, 30, 28, 3, 4, 2, 26, 51, 1, 29, 24, 52, 11, 6] x
  shift := 1
  point := 36
  good := {x | x ∉ ({0,25,32,34} : Finset (ZMod 53))}
  zero_notMem := by decide
  point_mem := by decide
  period := by decide
  closed := by decide
  sum := by decide
  fixed := by decide

theorem exists_data_size (b : ℕ) (hb : b ∈ ({11,17,29,53} : Finset ℕ)) (k : ℕ) :
    ∃ (A : Type) (a : AddCommGroup A) (f : Fintype A) (D : @Data A a),
      @Fintype.card A f = b * 7^k ∧ Nat.card D.good = (b-4)*7^k := by
  induction k with
  | zero =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · refine ⟨ZMod 11, inferInstance, inferInstance, seed11, by simp, ?_⟩
      change Nat.card {x : ZMod 11 // x ∉ ({0,1,3,6} : Finset (ZMod 11))} = _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      all_goals norm_num <;> decide
    · refine ⟨ZMod 17, inferInstance, inferInstance, seed17, by simp, ?_⟩
      change Nat.card {x : ZMod 17 // x ∉ ({0,1,4,9} : Finset (ZMod 17))} = _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      all_goals norm_num <;> decide
    · refine ⟨ZMod 29, inferInstance, inferInstance, seed29, by simp, ?_⟩
      change Nat.card {x : ZMod 29 // x ∉ ({0,16,17,18} : Finset (ZMod 29))} = _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      all_goals norm_num <;> decide
    · refine ⟨ZMod 53, inferInstance, inferInstance, seed53, by simp, ?_⟩
      change Nat.card {x : ZMod 53 // x ∉ ({0,25,32,34} : Finset (ZMod 53))} = _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      all_goals norm_num <;> decide
  | succ k ih =>
    obtain ⟨A,a,f,D,hm,hg⟩ := ih
    letI := a
    letI := f
    exact ⟨A × ZMod 7, inferInstance, inferInstance, D.timesSeven,
      by simp [Fintype.card_prod, hm, pow_succ, Nat.mul_assoc],
      by rw [D.timesSeven_card, hg, pow_succ, Nat.mul_assoc]⟩

theorem core_size {n : ℕ} (hn : 15 ≤ n) :
    ∃ b ∈ ({11,17,29,53} : Finset ℕ), ∃ k : ℕ,
      (b+4)*7^k ≤ n ∧ n < 2*(b*7^k) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h105 : n < 105
    · by_cases h22 : n < 22
      · exact ⟨11, by simp, 0, by norm_num; omega, by norm_num; omega⟩
      · by_cases h34 : n < 34
        · exact ⟨17, by simp, 0, by norm_num; omega, by norm_num; omega⟩
        · by_cases h58 : n < 58
          · exact ⟨29, by simp, 0, by norm_num; omega, by norm_num; omega⟩
          · exact ⟨53, by simp, 0, by norm_num; omega, by norm_num; omega⟩
    · obtain ⟨b,hb,k,hlo,hhi⟩ := ih (n/7) (by omega) (by omega)
      refine ⟨b,hb,k+1,?_,?_⟩ <;> rw [pow_succ]
      · have h' : 7*((b+4)*7^k) ≤ n := by omega
        nlinarith
      · have h' : n < 7*(2*(b*7^k)) := by omega
        nlinarith

end Spectrum.Cyclic481

namespace Spectrum

theorem models_481 {n : ℕ} (h : n ∈ positiveExcept {3,6}) : Law481.HasModel n := by
  have hn : 0 < n ∧ n ≠ 3 ∧ n ≠ 6 := by simpa [positiveExcept] using h
  by_cases h7 : n = 7
  · subst n; exact NoteWitness.model_481_7
  by_cases hr : n % 3 = 0
  · have h2 : Law481.HasModel 2 := (loops_481 (by norm_num [residues])).2
    have h4 : Law481.HasModel 4 := (loops_481 (by norm_num [residues])).2
    by_cases h9 : n = 9
    · subst n; exact NoteWitness.model_481_9
    by_cases h12 : n = 12
    · subst n; exact NoteWitness.model_481_12
    by_cases h18 : n = 18
    · subst n; exact NoteWitness.model_481_9.mul h2
    by_cases h24 : n = 24
    · subst n; exact NoteWitness.model_481_12.mul h2
    by_cases h36 : n = 36
    · subst n; exact NoteWitness.model_481_9.mul h4
    by_cases h60 : n = 60
    · subst n; exact NoteWitness.model_481_15.mul h4
    obtain ⟨b,hb,k,hlo,hhi⟩ := Cyclic481.core_size (show 15 ≤ n by omega)
    obtain ⟨A,a,f,D,hm,hg⟩ := Cyclic481.exists_data_size b hb k
    letI := a
    letI := f
    have hb4 : 4 ≤ b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> omega
    have hpow : 0 < 7^k := pow_pos (by decide) _
    have hmod : Fintype.card A % 3 = 2 := by
      rw [hm, Nat.mul_mod, Nat.pow_mod]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> norm_num
    apply D.model n
    · rw [hm]; nlinarith
    · rwa [hm]
    · rw [hm, hg]
      have he : (b-4)*7^k = b*7^k-4*7^k := Nat.sub_mul _ _ _
      have hle : 4*7^k ≤ b*7^k := Nat.mul_le_mul_right _ hb4
      rw [Nat.add_mul] at hlo
      omega
    · exact hmod
    · exact hr
    · rw [hm]
      intro he
      have hn' : n = b*7^k+7 := by omega
      by_cases hk : k = 0
      · subst k
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl | rfl <;> norm_num at hn' <;> omega
      · have hpow7 : 7 ≤ 7^k := by
          simpa using (Nat.pow_le_pow_right (by decide : 0 < 7) (show 1 ≤ k by omega))
        nlinarith
  · exact (loops_481 (show n ∈ residues 3 {1,2} {7} from
      ⟨hn.1, by simp; omega, by simpa using h7⟩)).2

end Spectrum
