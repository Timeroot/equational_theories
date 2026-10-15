import equational_theories.Spectrum.Equation1486.SingletonRow
import Mathlib.Tactic

/-! Normalize square-row images, preserving elements that have already been
labelled. This is a permutation argument, not an enumeration of magmas. -/
namespace Spectrum.E1486.OrderTen
open SquareRows

/-- Equal-size subsets can be matched while fixing every specified point on
which their membership agrees. -/
theorem perm_sets_fixing {A : Type*} [Fintype A] [DecidableEq A]
    (S T F : Finset A) (hc : S.card = T.card)
    (hF : ∀ a ∈ F, a ∈ S ↔ a ∈ T) :
    ∃ p : Equiv.Perm A, (∀ a ∈ F, p a = a) ∧ ∀ x, p x ∈ T ↔ x ∈ S := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    let e : S ≃ T := Classical.choice (Fintype.card_eq.mp (by simpa using hc))
    refine ⟨e.extendSubtype, by simp, fun x => ⟨?_, e.extendSubtype_mem x⟩⟩
    intro hx
    by_contra hn
    exact e.extendSubtype_not_mem x hn hx
  | @insert a F ha ih =>
    obtain ⟨p,hfix,hp⟩ := ih (fun x hx => hF x (Finset.mem_insert_of_mem hx))
    let q := Equiv.swap (p a) a
    have hmem : p a ∈ T ↔ a ∈ T := (hp a).trans (hF a (by simp))
    have hswap (y : A) : q y ∈ T ↔ y ∈ T := by
      by_cases hy : y = p a
      · subst y; simpa [q] using hmem.symm
      by_cases hy' : y = a
      · subst y; simpa [q] using hmem
      simp [q, Equiv.swap_apply_of_ne_of_ne hy hy']
    refine ⟨p.trans q, ?_, fun x => (hswap (p x)).trans (hp x)⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp [q]
    · change q (p x) = x
      rw [hfix x hx]
      have hxa : x ≠ a := by intro he; subst x; exact ha hx
      have hxp : x ≠ p a := by
        intro he
        have : p x = p a := (hfix x hx).trans he
        exact hxa (p.injective this)
      exact Equiv.swap_apply_of_ne_of_ne hxp hxa

def relabel {A : Type*} (f : A → A → A) (p : Equiv.Perm A) :=
  fun x y => p (f (p.symm x) (p.symm y))

theorem relabel_law {A : Type*} (f : A → A → A) (p : Equiv.Perm A)
    (h : Lawful f) : Lawful (relabel f p) := by
  intro x y z
  simp only [relabel, Equiv.symm_apply_apply]
  rw [h, Equiv.apply_symm_apply]

theorem row_relabel {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → A → A) (p : Equiv.Perm A) (x : A) :
    row (relabel f p) x = (row f (p.symm x)).image p := by
  ext z
  simp only [mem_row, Finset.mem_image, relabel, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨y,hy⟩; exact ⟨_,⟨p.symm y,rfl⟩,hy⟩
  · rintro ⟨w,⟨y,hy⟩,hz⟩
    exact ⟨p y, by simpa [hy] using hz⟩

theorem row_bound (f : Fin 10 → Fin 10 → Fin 10) (h : Lawful f)
    (k : ℕ) (hk : ∀ a, k ≤ (row f a).card) (x : Fin 10) :
    k * (row f x).card ≤ 10 := by
  have hs : ∑ a ∈ row f x, k ≤ ∑ a ∈ row f x, (row f a).card :=
    Finset.sum_le_sum (fun a _ => hk a)
  have hc := Finset.card_le_card (Finset.subset_univ ((row f x).biUnion (row f)))
  rw [Finset.card_biUnion (row_disjoint f h x)] at hc
  simp only [Finset.card_univ,Fintype.card_fin] at hc
  simpa [Nat.mul_comm] using hs.trans hc

/-- With no rank-two row, every row of a ten-element model has rank three. -/
theorem three_of_no_two (f : Fin 10 → Fin 10 → Fin 10) (h : Lawful f)
    (hn : ∀ a, (row f a).card ≠ 2) : ∀ a, (row f a).card = 3 := by
  have hl (a : Fin 10) : 3 ≤ (row f a).card := by
    have := two_le_row_card f h a
    have := hn a
    omega
  intro a
  have := row_bound f h 3 hl a
  have := hl a
  omega


abbrev Ten := Fin 10

def target (k : ℕ) (inside : Bool) : Finset Ten :=
  Finset.univ.filter fun x => if inside then x.val < k else 0 < x.val ∧ x.val ≤ k

theorem image_eq_target {A : Type*} [DecidableEq A] (S T : Finset A)
    (p : Equiv.Perm A) (h : ∀ x, p x ∈ T ↔ x ∈ S) : S.image p = T := by
  ext x
  constructor
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (h y).mpr hy
  · intro hx
    exact Finset.mem_image.mpr ⟨p.symm x,(h _).mp (by simpa using hx),p.apply_symm_apply x⟩

theorem image_fixed {A : Type*} [DecidableEq A] (S : Finset A)
    (p : Equiv.Perm A) (h : ∀ x ∈ S, p x = x) : S.image p = S := by
  simpa using (Finset.image_congr h : S.image p = S.image id)

theorem symm_fixed {A : Type*} (p : Equiv.Perm A) {x : A} (h : p x = x) :
    p.symm x = x := by apply p.injective; simpa using h.symm

theorem rank_relabel (f : Ten → Ten → Ten) (p : Equiv.Perm Ten) (k : ℕ)
    (h : ∀ x, (row f x).card = k) : ∀ x, (row (relabel f p) x).card = k := by
  intro x
  rw [row_relabel,Finset.card_image_of_injective _ p.injective,h]

/-- Label a chosen row while keeping its chosen vertex at zero. -/
theorem normalize_at (f : Ten → Ten → Ten) (a : Ten) (k : ℕ)
    (hk : k = 2 ∨ k = 3) (hr : (row f a).card = k) :
    ∃ p : Equiv.Perm Ten, ∃ inside : Bool,
      p a = 0 ∧ row (relabel f p) 0 = target k inside := by
  classical
  let p := Equiv.swap a 0
  let f' := relabel f p
  have hp0 : p.symm 0 = a := by simp [p]
  have hcard : (row f' 0).card = k := by
    simp only [f',row_relabel,hp0,Finset.card_image_of_injective _ p.injective,hr]
  let inside := decide ((0 : Ten) ∈ row f' 0)
  have htc : (target k inside).card = k := by
    rcases hk with rfl | rfl <;> cases inside <;> decide
  have htz : (0 : Ten) ∈ row f' 0 ↔ (0 : Ten) ∈ target k inside := by
    have hkpos : 0 < k := by omega
    by_cases hz : (0 : Ten) ∈ row f' 0 <;> simp [target,inside,hz,hkpos]
  obtain ⟨q,hqfix,hq⟩ := perm_sets_fixing (row f' 0) (target k inside) {0}
    (hcard.trans htc.symm) (by simpa using htz)
  have hq0 : q 0 = 0 := hqfix 0 (by simp)
  refine ⟨p.trans q,inside,?_,?_⟩
  · simp [p,hq0]
  · have hc : relabel f (p.trans q) = relabel f' q := by
      funext x y; simp [relabel,f']
    rw [hc,row_relabel,symm_fixed q hq0]
    exact image_eq_target _ _ q hq


def B0 : Finset Ten := {0,1,2}
def B1 : Finset Ten := {3,4,5}
def B2 : Finset Ten := {6,7,8}

theorem preserve_row (f : Ten → Ten → Ten) (p : Equiv.Perm Ten)
    (F : Finset Ten) (hf : ∀ a ∈ F, p a = a) (x : Ten) (hx : x ∈ F)
    (hr : row f x ⊆ F) : row (relabel f p) x = row f x := by
  rw [row_relabel,symm_fixed p (hf x hx)]
  exact image_fixed _ p (fun a ha => hf a (hr ha))

/-- The three disjoint second-step images can be labelled as three blocks,
while preserving zero and the first block. -/
theorem normalize_blocks (f : Ten → Ten → Ten) (h : Lawful f)
    (hr : ∀ x, (row f x).card = 3) (h0 : row f 0 = B0) :
    ∃ p : Equiv.Perm Ten, p 0 = 0 ∧
      row (relabel f p) 0 = B0 ∧ row (relabel f p) 1 = B1 ∧
      row (relabel f p) 2 = B2 := by
  classical
  have hdis (a b : Ten) (ha : a ∈ B0) (hb : b ∈ B0) (hab : a ≠ b) :
      Disjoint (row f a) (row f b) :=
    row_disjoint f h 0 (by simpa [h0] using ha) (by simpa [h0] using hb) hab
  have hd10 : Disjoint (row f 1) B0 := by
    rw [← h0]; exact hdis 1 0 (by decide) (by decide) (by decide)
  obtain ⟨p,hpfix,hp⟩ := perm_sets_fixing (row f 1) B1 B0
    ((hr 1).trans (by decide)) (by
      intro a ha
      have hs : a ∉ row f 1 := Finset.disjoint_right.mp hd10 ha
      have ht : a ∉ B1 := Finset.disjoint_right.mp (by decide : Disjoint B1 B0) ha
      simp [hs,ht])
  let g := relabel f p
  have hg : Lawful g := relabel_law f p h
  have hgr := rank_relabel f p 3 hr
  have hg0 : row g 0 = B0 := by
    rw [preserve_row f p B0 hpfix 0 (by decide) (by rw [h0]),h0]
  have hg1 : row g 1 = B1 := by
    rw [row_relabel,symm_fixed p (hpfix 1 (by decide))]
    exact image_eq_target _ _ p hp
  have hd2 (b : Ten) (hb : b ∈ B0) (h2b : (2 : Ten) ≠ b) :
      Disjoint (row g 2) (row g b) :=
    row_disjoint g hg 0 (by rw [hg0]; decide) (by rwa [hg0]) h2b
  have hd2F : Disjoint (row g 2) (B0 ∪ B1) := by
    rw [Finset.disjoint_union_right,← hg0,← hg1]
    exact ⟨hd2 0 (by decide) (by decide),hd2 1 (by decide) (by decide)⟩
  obtain ⟨q,hqfix,hq⟩ := perm_sets_fixing (row g 2) B2 (B0 ∪ B1)
    ((hgr 2).trans (by decide)) (by
      intro a ha
      have hs : a ∉ row g 2 := Finset.disjoint_right.mp hd2F ha
      have ht : a ∉ B2 := Finset.disjoint_right.mp
        (by decide : Disjoint B2 (B0 ∪ B1)) ha
      simp [hs,ht])
  have hc : relabel f (p.trans q) = relabel g q := by
    funext x y; simp [relabel,g]
  refine ⟨p.trans q,?_,?_⟩
  · change q (p 0) = 0
    rw [hpfix 0 (by decide),hqfix 0 (by decide)]
  · rw [hc]
    refine ⟨?_,?_,?_⟩
    · rw [preserve_row g q (B0 ∪ B1) hqfix 0 (by decide)
        (by rw [hg0]; exact Finset.subset_union_left),hg0]
    · rw [preserve_row g q (B0 ∪ B1) hqfix 1 (by decide)
        (by rw [hg1]; exact Finset.subset_union_right),hg1]
    · rw [row_relabel,symm_fixed q (hqfix 2 (by decide))]
      exact image_eq_target _ _ q hq


theorem normalize_two (f : Ten → Ten → Ten) (h : Lawful f)
    (he : ∃ a, (row f a).card = 2) :
    ∃ g : Ten → Ten → Ten, ∃ inside : Bool,
      Lawful g ∧ row g 0 = target 2 inside := by
  obtain ⟨a,ha⟩ := he
  obtain ⟨p,inside,_,hp⟩ := normalize_at f a 2 (Or.inl rfl) ha
  exact ⟨relabel f p,inside,relabel_law f p h,hp⟩

theorem nonidem_relabel (f : Ten → Ten → Ten) (p : Equiv.Perm Ten)
    (h : ∀ x, f x x ≠ x) : ∀ x, relabel f p x x ≠ x := by
  intro x hx
  apply h (p.symm x)
  simpa [relabel] using congrArg p.symm hx

theorem idem_relabel (f : Ten → Ten → Ten) (p : Equiv.Perm Ten)
    (a : Ten) (ha : p a = 0) (hi : f a a = a) : relabel f p 0 0 = 0 := by
  have hp : p.symm 0 = a := by apply p.injective; simp [ha]
  simp [relabel,hp,hi,ha]

theorem normalize_three_idem (f : Ten → Ten → Ten) (h : Lawful f)
    (hr : ∀ x, (row f x).card = 3) (he : ∃ a, f a a = a) :
    ∃ g : Ten → Ten → Ten, Lawful g ∧ (∀ x, (row g x).card = 3) ∧
      row g 0 = target 3 true ∧ g 0 0 = 0 ∧ row g 1 = B1 ∧ row g 2 = B2 := by
  obtain ⟨a,ha⟩ := he
  obtain ⟨p,inside,hpa,hrow⟩ := normalize_at f a 3 (Or.inr rfl) (hr a)
  let g := relabel f p
  have hg := relabel_law f p h
  have hgr := rank_relabel f p 3 hr
  have hgi : g 0 0 = 0 := idem_relabel f p a hpa ha
  have hin : inside = true := by
    have hm : (0 : Ten) ∈ row g 0 := (mem_row g 0 0).mpr ⟨0,by rw [hgi,hgi]⟩
    rw [hrow] at hm
    cases inside <;> simp_all [target]
  subst inside
  have hB : target 3 true = B0 := by decide
  obtain ⟨q,hq0,hqB0,hqB1,hqB2⟩ := normalize_blocks g hg hgr (hrow.trans hB)
  exact ⟨relabel g q,relabel_law g q hg,rank_relabel g q 3 hgr,
    hqB0.trans hB.symm,idem_relabel g q 0 hq0 hgi,hqB1,hqB2⟩

theorem normalize_three_noidem (f : Ten → Ten → Ten) (h : Lawful f)
    (hr : ∀ x, (row f x).card = 3) (hi : ∀ x, f x x ≠ x) :
    ∃ g : Ten → Ten → Ten, ∃ inside : Bool, Lawful g ∧
      (∀ x, (row g x).card = 3) ∧ row g 0 = target 3 inside ∧
      (∃ z, g z z = 0) ∧ (∀ x, g x x ≠ x) ∧ g 0 0 = 1 ∧ g 1 1 = 0 := by
  let a := f 0 0
  obtain ⟨p,inside,hpa,hrow⟩ := normalize_at f a 3 (Or.inr rfl) (hr a)
  let g := relabel f p
  have hg := relabel_law f p h
  have hgr := rank_relabel f p 3 hr
  have hgi := nonidem_relabel f p hi
  have hs : ∃ z, g z z = 0 := ⟨p 0, by
    simp only [g,relabel,Equiv.symm_apply_apply]
    exact hpa⟩
  let b := g 0 0
  have hb0 : b ≠ 0 := hgi 0
  have hb : b ∈ target 3 inside := by
    rw [← hrow]
    obtain ⟨z,hz⟩ := hs
    exact (mem_row g 0 b).mpr ⟨z,by rw [hz]⟩
  have h1 : (1 : Ten) ∈ target 3 inside := by cases inside <;> decide
  let q := Equiv.swap b (1 : Ten)
  have hq0 : q 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm hb0) (by decide)
  have hqi : q.symm 0 = 0 := symm_fixed q hq0
  have himage : (target 3 inside).image q = target 3 inside := by
    apply image_eq_target
    intro x
    by_cases hx : x = b
    · subst x; simp [q,hb,h1]
    by_cases hx' : x = 1
    · subst x; simp [q,hb,h1]
    simp [q,Equiv.swap_apply_of_ne_of_ne hx hx']
  have hz : relabel g q 0 0 = 1 := by
    change q (g (q.symm 0) (q.symm 0)) = 1
    rw [hqi]
    exact Equiv.swap_apply_left b 1
  have hs' : ∃ z, relabel g q z z = 0 := by
    obtain ⟨z,hz⟩ := hs
    exact ⟨q z,by simp [relabel,hz,hq0]⟩
  have hback : relabel g q 1 1 = 0 := by
    obtain ⟨z,hz'⟩ := hs'
    have hh := square_tripotent (relabel g q) (relabel_law g q hg) z
    simpa only [hz',hz] using hh
  refine ⟨relabel g q,inside,relabel_law g q hg,rank_relabel g q 3 hgr,
    ?_,hs',nonidem_relabel g q hgi,hz,hback⟩
  rw [row_relabel,hqi,hrow,himage]

end Spectrum.E1486.OrderTen
