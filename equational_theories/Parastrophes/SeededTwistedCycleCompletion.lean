import equational_theories.Mathlib.Order.Greedy
import Mathlib.Tactic

/-!
# Twisted-cycle completion with prescribed adjacent products

Each block is an integer grid. C shifts the vertical coordinate and T shifts
horizontally. We prescribe D(a,Ca)=Ta and D(a,Ta)=C²a, together with their
cyclic consequences. Fresh blocks then fill every other product.
-/
namespace Parastrophes.SeededTwistedCycleCompletion
noncomputable section
abbrev Point := Nat × Int × Int

def shift (k : Int) (a : Point) : Point := (a.1,a.2.1,a.2.2+k)
def next (a : Point) : Point := (a.1,a.2.1+1,a.2.2)
@[simp] theorem shift_zero (a : Point) : shift 0 a=a := by rcases a with ⟨a,i,j⟩; simp [shift]
@[simp] theorem shift_shift (i j : Int) (a : Point) :
    shift i (shift j a)=shift (j+i) a := by simp [shift,add_assoc]
@[simp] theorem shift_next (k : Int) (a : Point) : shift k (next a)=next (shift k a) := rfl
@[simp] theorem shift_fst (k : Int) (a : Point) : (shift k a).1=a.1 := rfl
@[simp] theorem shift_height (k : Int) (a : Point) : (shift k a).2.2=a.2.2+k := rfl

def Seed (x y z : Point) : Prop := ∃ a,
  (x=a ∧ y=shift 1 a ∧ z=next a) ∨
  (x=shift 1 a ∧ y=next a ∧ z=shift 1 a) ∨
  (x=next a ∧ y=shift 1 a ∧ z=shift 2 a) ∨
  (x=a ∧ y=next a ∧ z=shift 2 a) ∨
  (x=next a ∧ y=shift 2 a ∧ z=shift 1 a) ∨
  (x=shift 2 a ∧ y=shift 1 a ∧ z=shift 1 (next a))

theorem seed_functional {x y z w : Point} (h : Seed x y z) (h' : Seed x y w) : z=w := by
  obtain ⟨a,h⟩ := h
  obtain ⟨b,h'⟩ := h'
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals
    rcases h' with ⟨hx,hy,rfl⟩ | ⟨hx,hy,rfl⟩ | ⟨hx,hy,rfl⟩ |
      ⟨hx,hy,rfl⟩ | ⟨hx,hy,rfl⟩ | ⟨hx,hy,rfl⟩
    all_goals
      have hx1 := congrArg Prod.fst hx
      have hx2 := congrArg (fun p : Point => p.2.1) hx
      have hx3 := congrArg (fun p : Point => p.2.2) hx
      have hy2 := congrArg (fun p : Point => p.2.1) hy
      have hy3 := congrArg (fun p : Point => p.2.2) hy
      apply Prod.ext
      · simpa only [shift,next] using hx1
      · apply Prod.ext <;> simp only [shift,next] at * <;> omega

theorem seed_rotate {x y z : Point} (h : Seed x y z) : Seed y z (shift 1 x) := by
  obtain ⟨a,h⟩ := h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact ⟨x,Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)⟩
  · exact ⟨a,Or.inr (Or.inr (Or.inl ⟨rfl,rfl,by simp⟩))⟩
  · exact ⟨shift 1 a,Or.inl ⟨rfl,by simp,by simp⟩⟩
  · exact ⟨x,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩))))⟩
  · exact ⟨a,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl,rfl⟩))))⟩
  · exact ⟨shift 1 a,Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,by simp,by simp⟩)))⟩

theorem seed_translate {x y z : Point} (h : Seed x y z) (k : Int) :
    Seed (shift k x) (shift k y) (shift k z) := by
  obtain ⟨a,h⟩ := h
  refine ⟨shift k a,?_⟩
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals simp [shift,next,add_right_comm]

theorem seed_same_block {x y z : Point} (h : Seed x y z) : x.1=y.1 := by
  obtain ⟨a,h⟩ := h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals rfl

theorem seed_lower {x y z : Point} (h : Seed x y z) : min x.2.2 y.2.2 ≤ z.2.2 := by
  obtain ⟨a,h⟩ := h
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals simp only [shift,next]; omega

/-- A prescribed collection of products, closed under the twisted cycle and
integer shifts. Products stay within a block until the completion adds them. -/
structure SeedData where
  R : Point → Point → Point → Prop
  functional : ∀ a b c d, R a b c → R a b d → c=d
  rotate : ∀ a b c, R a b c → R b c (shift 1 a)
  translate : ∀ a b c, R a b c → ∀ k, R (shift k a) (shift k b) (shift k c)
  same_block : ∀ a b c, R a b c → a.1=b.1
  lower : ∀ a b c, R a b c → min a.2.2 b.2.2 ≤ c.2.2

def seed1695 : SeedData :=
  ⟨Seed,fun _ _ _ _ => seed_functional,fun _ _ _ => seed_rotate,
    fun _ _ _ => seed_translate,fun _ _ _ => seed_same_block,fun _ _ _ => seed_lower⟩

structure Partial (seed : SeedData := seed1695) where
  R : Point → Point → Point → Prop
  functional : ∀ a b c d, R a b c → R a b d → c=d
  rotate : ∀ a b c, R a b c → R b c (shift 1 a)
  translate : ∀ a b c, R a b c → ∀ k, R (shift k a) (shift k b) (shift k c)
  seeded : ∀ a b c, seed.R a b c → R a b c
  lower : ∀ a b c, R a b c → min a.2.2 b.2.2 ≤ c.2.2
  support : Finset Nat
  supported : ∀ a b c, R a b c → seed.R a b c ∨
    (a.1 ∈ support ∧ b.1 ∈ support ∧ c.1 ∈ support)

namespace Partial
variable {seed : SeedData}
instance : Preorder (Partial seed) where
  le p q := ∀ a b c, p.R a b c → q.R a b c
  le_refl _ := fun _ _ _ h => h
  le_trans _ _ _ hp hq := fun _ _ _ h => hq _ _ _ (hp _ _ _ h)

def empty (seed : SeedData := seed1695) : Partial seed where
  R := seed.R
  functional := seed.functional
  rotate := seed.rotate
  translate := seed.translate
  seeded := fun _ _ _ h => h
  lower := seed.lower
  support := ∅
  supported := fun _ _ _ h => Or.inl h

def New (a b c x y z : Point) : Prop :=
  (∃ k, x=shift k a ∧ y=shift k b ∧ z=shift k c) ∨
  (∃ k, x=shift k b ∧ y=shift k c ∧ z=shift (k+1) a) ∨
  (∃ k, x=shift k c ∧ y=shift (k+1) a ∧ z=shift (k+1) b)

private theorem new_rotate {a b c x y z : Point} (h : New a b c x y z) :
    New a b c y z (shift 1 x) := by
  rcases h with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
  · exact Or.inr (Or.inl ⟨k,rfl,rfl,by simp⟩)
  · exact Or.inr (Or.inr ⟨k,rfl,rfl,by simp⟩)
  · exact Or.inl ⟨k+1,rfl,rfl,by simp⟩

private theorem new_translate {a b c x y z : Point} (h : New a b c x y z) (j : Int) :
    New a b c (shift j x) (shift j y) (shift j z) := by
  rcases h with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
  · exact Or.inl ⟨k+j,by simp,by simp,by simp⟩
  · exact Or.inr (Or.inl ⟨k+j,by simp,by simp,by simp [add_right_comm]⟩)
  · exact Or.inr (Or.inr ⟨k+j,by simp,by simp [add_right_comm],by simp [add_right_comm]⟩)

private theorem new_functional {a b c : Point} (hbc : b.1 ≠ c.1)
    {x y z w : Point} (h : New a b c x y z) (h' : New a b c x y w) : z=w := by
  rcases h with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
  all_goals
    rcases h' with ⟨j,hx,hy,rfl⟩ | ⟨j,hx,hy,rfl⟩ | ⟨j,hx,hy,rfl⟩
    all_goals
      have hx1 := congrArg Prod.fst hx
      have hx3 := congrArg (fun p : Point => p.2.2) hx
      have hy1 := congrArg Prod.fst hy
      have hy3 := congrArg (fun p : Point => p.2.2) hy
      simp only [shift_fst,shift_height] at hx1 hx3 hy1 hy3
      first
      | exact False.elim (by omega)
      | have hk : k=j := by omega
        subst j
        rfl

private theorem old_new_disjoint (p : Partial seed) {a b c : Point}
    (hc : c.1 ∉ p.support) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1)
    (missing : ∀ z, ¬ p.R a b z)
    {x y z w : Point} (ho : p.R x y z) (hn : New a b c x y w) : False := by
  rcases hn with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
  · have h := p.translate _ _ _ ho (-k)
    simp only [shift_shift,add_neg_cancel,shift_zero] at h
    exact missing _ h
  · rcases p.supported _ _ _ ho with h | h
    · apply hbc
      simpa only [shift_fst] using seed.same_block _ _ _ h
    · exact hc h.2.1
  · rcases p.supported _ _ _ ho with h | h
    · apply hac
      simpa only [shift_fst] using (seed.same_block _ _ _ h).symm
    · exact hc h.1

/-- The preassigned grid products do not interfere with a fresh block. -/
def insert (p : Partial seed) (a b : Point) (n : Nat)
    (hn : n ∉ p.support) (han : a.1 ≠ n) (hbn : b.1 ≠ n)
    (missing : ∀ z, ¬ p.R a b z) : Partial seed := by
  let c : Point := (n,0,min a.2.2 b.2.2)
  refine ⟨fun x y z => p.R x y z ∨ New a b c x y z, ?_, ?_, ?_, ?_, ?_,
    p.support ∪ {a.1,b.1,n}, ?_⟩
  · intro x y z w hz hw
    rcases hz with hz | hz <;> rcases hw with hw | hw
    · exact p.functional _ _ _ _ hz hw
    · exact False.elim (old_new_disjoint p hn han hbn missing hz hw)
    · exact False.elim (old_new_disjoint p hn han hbn missing hw hz)
    · exact new_functional hbn hz hw
  · intro x y z h
    exact h.elim (fun h => Or.inl (p.rotate _ _ _ h)) (fun h => Or.inr (new_rotate h))
  · intro x y z h k
    exact h.elim (fun h => Or.inl (p.translate _ _ _ h k))
      (fun h => Or.inr (new_translate h k))
  · intro x y z h; exact Or.inl (p.seeded _ _ _ h)
  · intro x y z h
    rcases h with h | h
    · exact p.lower _ _ _ h
    rcases h with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
    all_goals simp only [shift_height,c]; omega
  · intro x y z h
    rcases h with h | h
    · rcases p.supported _ _ _ h with hs | hs
      · exact Or.inl hs
      · exact Or.inr ⟨Finset.mem_union_left _ hs.1,
          Finset.mem_union_left _ hs.2.1,Finset.mem_union_left _ hs.2.2⟩
    apply Or.inr
    rcases h with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
    all_goals simp [c]

theorem le_insert (p : Partial seed) (a b : Point) n hn han hbn missing :
    p ≤ p.insert a b n hn han hbn missing := fun _ _ _ h => Or.inl h

theorem insert_covers (p : Partial seed) (a b : Point) n hn han hbn missing :
    (p.insert a b n hn han hbn missing).R a b (n,0,min a.2.2 b.2.2) :=
  Or.inr (Or.inl ⟨0,by simp,by simp,by simp⟩)

end Partial

structure Completed (seed : SeedData := seed1695) where
  R : Point → Point → Point → Prop
  functional : ∀ a b c d, R a b c → R a b d → c=d
  rotate : ∀ a b c, R a b c → R b c (shift 1 a)
  translate : ∀ a b c, R a b c → ∀ k, R (shift k a) (shift k b) (shift k c)
  seeded : ∀ a b c, seed.R a b c → R a b c
  lower : ∀ a b c, R a b c → min a.2.2 b.2.2 ≤ c.2.2
  total : ∀ a b, ∃ c, R a b c

theorem exists_completed (seed : SeedData := seed1695) : Nonempty (Completed seed) := by
  classical
  obtain ⟨chain,hchain,_,_,hcover⟩ := exists_greedy_chain
    (fun ab : Point × Point => {p : Partial seed | ∃ c, p.R ab.1 ab.2 c}) (fun p ab => by
      by_cases hex : ∃ c, p.R ab.1 ab.2 c
      · exact ⟨p,le_rfl,hex⟩
      have missing : ∀ c, ¬ p.R ab.1 ab.2 c := by simpa using hex
      obtain ⟨n,hn⟩ := Infinite.exists_notMem_finset (insert ab.1.1 (insert ab.2.1 p.support))
      have hs : n ∉ p.support := fun h => hn (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      have ha : ab.1.1 ≠ n := fun h => hn (h ▸ Finset.mem_insert_self _ _)
      have hb : ab.2.1 ≠ n := fun h => hn (Finset.mem_insert_of_mem (h ▸ Finset.mem_insert_self _ _))
      exact ⟨p.insert ab.1 ab.2 n hs ha hb missing,
        Partial.le_insert p ab.1 ab.2 n hs ha hb missing,
        ⟨_,Partial.insert_covers p ab.1 ab.2 n hs ha hb missing⟩⟩) (Partial.empty seed)
  let R := fun a b c => ∃ p ∈ chain, p.R a b c
  refine ⟨⟨R,?_,?_,?_,?_,?_,?_⟩⟩
  · rintro a b c d ⟨p,hp,hc⟩ ⟨q,hq,hd⟩
    rcases eq_or_ne p q with rfl | hne
    · exact p.functional _ _ _ _ hc hd
    rcases hchain hp hq hne with hpq | hqp
    · exact q.functional _ _ _ _ (hpq _ _ _ hc) hd
    · exact p.functional _ _ _ _ hc (hqp _ _ _ hd)
  · rintro a b c ⟨p,hp,h⟩; exact ⟨p,hp,p.rotate _ _ _ h⟩
  · rintro a b c ⟨p,hp,h⟩ k; exact ⟨p,hp,p.translate _ _ _ h k⟩
  · intro a b c h
    obtain ⟨p,hp,_⟩ := hcover (a,b)
    exact ⟨p,hp,p.seeded _ _ _ h⟩
  · rintro a b c ⟨p,_,h⟩; exact p.lower _ _ _ h
  · intro a b
    obtain ⟨p,hp,c,hc⟩ := hcover (a,b)
    exact ⟨c,p,hp,hc⟩

def complete (seed : SeedData := seed1695) : Completed seed := Classical.choice (exists_completed seed)
end
end Parastrophes.SeededTwistedCycleCompletion
