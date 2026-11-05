import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic

/-!
# Completing a quasigroup with twisted three-cycles

The nonidentity elements are integer-indexed orbits. The shift `C(i,n)=(i,n+1)`
rotates a multiplication triple `(a,b,c)` to `(b,c,C a)`. Fresh orbits fill
undefined products while preserving a lower bound on the output's height.
-/
namespace Parastrophes.TwistedCycleCompletion
noncomputable section
abbrev Point := Nat × Int

def shift (k : Int) (a : Point) : Point := (a.1,a.2+k)
@[simp] theorem shift_zero (a : Point) : shift 0 a=a := by cases a; simp [shift]
@[simp] theorem shift_shift (i j : Int) (a : Point) :
    shift i (shift j a)=shift (j+i) a := by simp [shift,add_assoc]
@[simp] theorem shift_fst (k : Int) (a : Point) : (shift k a).1=a.1 := rfl
@[simp] theorem shift_snd (k : Int) (a : Point) : (shift k a).2=a.2+k := rfl

theorem shift_injective (k : Int) : Function.Injective (shift k) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  simpa [shift] using h

structure Partial where
  R : Point → Point → Point → Prop
  functional : ∀ a b c d, R a b c → R a b d → c=d
  rotate : ∀ a b c, R a b c → R b c (shift 1 a)
  translate : ∀ a b c, R a b c → ∀ k, R (shift k a) (shift k b) (shift k c)
  avoid : ∀ a b c, R a b c → b ≠ shift 1 a
  lower : ∀ a b c, R a b c → min a.2 b.2 ≤ c.2
  support : Finset Nat
  supported : ∀ a b c, R a b c → a.1 ∈ support ∧ b.1 ∈ support ∧ c.1 ∈ support

namespace Partial
instance : Preorder Partial where
  le p q := ∀ a b c, p.R a b c → q.R a b c
  le_refl _ := fun _ _ _ h => h
  le_trans _ _ _ hp hq := fun _ _ _ h => hq _ _ _ (hp _ _ _ h)

def empty : Partial where
  R := fun _ _ _ => False
  functional := by simp
  rotate := by simp
  translate := by simp
  avoid := by simp
  lower := by simp
  support := ∅
  supported := by simp

/-- The three phases of an entire shift orbit of multiplication triples. -/
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

private theorem new_functional {a b c : Point} (_hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1)
    {x y z w : Point} (h : New a b c x y z) (h' : New a b c x y w) : z=w := by
  rcases h with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
  all_goals
    rcases h' with ⟨j,hx,hy,rfl⟩ | ⟨j,hx,hy,rfl⟩ | ⟨j,hx,hy,rfl⟩
    all_goals simp only [shift, Prod.mk.injEq] at hx hy ⊢
    all_goals first | omega | exact ⟨trivial,by omega⟩

private theorem old_new_disjoint (p : Partial) {a b c : Point}
    (hc : c.1 ∉ p.support) (missing : ∀ z, ¬ p.R a b z)
    {x y z w : Point} (ho : p.R x y z) (hn : New a b c x y w) : False := by
  rcases hn with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
  · have h := p.translate _ _ _ ho (-k)
    simp only [shift_shift, add_neg_cancel, shift_zero] at h
    exact missing _ h
  · exact hc (p.supported _ _ _ ho).2.1
  · exact hc (p.supported _ _ _ ho).1

/-- Fill one missing product with a fresh orbit at the lower input height. -/
def insert (p : Partial) (a b : Point) (n : Nat)
    (hn : n ∉ p.support) (han : a.1 ≠ n) (hbn : b.1 ≠ n)
    (hab : b ≠ shift 1 a) (missing : ∀ z, ¬ p.R a b z) : Partial := by
  let c : Point := (n,min a.2 b.2)
  refine ⟨fun x y z => p.R x y z ∨ New a b c x y z, ?_, ?_, ?_, ?_, ?_,
    p.support ∪ {a.1,b.1,n}, ?_⟩
  · intro x y z w hz hw
    rcases hz with hz | hz <;> rcases hw with hw | hw
    · exact p.functional _ _ _ _ hz hw
    · exact False.elim (old_new_disjoint p hn missing hz hw)
    · exact False.elim (old_new_disjoint p hn missing hw hz)
    · exact new_functional han hbn hz hw
  · intro x y z h
    exact h.elim (fun h => Or.inl (p.rotate _ _ _ h)) (fun h => Or.inr (new_rotate h))
  · intro x y z h k
    exact h.elim (fun h => Or.inl (p.translate _ _ _ h k))
      (fun h => Or.inr (new_translate h k))
  · intro x y z h
    rcases h with h | h
    · exact p.avoid _ _ _ h
    rcases h with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
    · intro he
      apply hab
      apply shift_injective k
      simpa only [shift_shift,add_comm] using he
    · intro he; exact hbn (congrArg Prod.fst he).symm
    · intro he; exact han (congrArg Prod.fst he)
  · intro x y z h
    rcases h with h | h
    · exact p.lower _ _ _ h
    rcases h with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
    all_goals simp only [shift_snd, c]; omega
  · intro x y z h
    rcases h with h | h
    · exact ⟨Finset.mem_union_left _ (p.supported _ _ _ h).1,
        Finset.mem_union_left _ (p.supported _ _ _ h).2.1,
        Finset.mem_union_left _ (p.supported _ _ _ h).2.2⟩
    rcases h with ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩ | ⟨k,rfl,rfl,rfl⟩
    all_goals simp [c]

theorem le_insert (p : Partial) (a b : Point) n hn han hbn hab missing :
    p ≤ p.insert a b n hn han hbn hab missing := fun _ _ _ h => Or.inl h

theorem insert_covers (p : Partial) (a b : Point) n hn han hbn hab missing :
    (p.insert a b n hn han hbn hab missing).R a b (n,min a.2 b.2) :=
  Or.inr (Or.inl ⟨0,by simp,by simp,by simp⟩)

end Partial

structure Completed where
  R : Point → Point → Point → Prop
  functional : ∀ a b c d, R a b c → R a b d → c=d
  rotate : ∀ a b c, R a b c → R b c (shift 1 a)
  translate : ∀ a b c, R a b c → ∀ k, R (shift k a) (shift k b) (shift k c)
  avoid : ∀ a b c, R a b c → b ≠ shift 1 a
  lower : ∀ a b c, R a b c → min a.2 b.2 ≤ c.2
  total : ∀ a b, b ≠ shift 1 a → ∃ c, R a b c

/-- The union of a chain filling every allowed pair. Each extension consumes
one fresh orbit, so only finitely many orbit labels are excluded at a stage. -/
theorem exists_completed : Nonempty Completed := by
  classical
  obtain ⟨chain,hchain,_,_,hcover⟩ := exists_greedy_chain
    (fun ab : Point × Point => {p : Partial |
      ab.2=shift 1 ab.1 ∨ ∃ c, p.R ab.1 ab.2 c}) (fun p ab => by
      by_cases hab : ab.2=shift 1 ab.1
      · exact ⟨p,le_rfl,Or.inl hab⟩
      by_cases hex : ∃ c, p.R ab.1 ab.2 c
      · exact ⟨p,le_rfl,Or.inr hex⟩
      have missing : ∀ c, ¬ p.R ab.1 ab.2 c := by simpa using hex
      obtain ⟨n,hn⟩ := Infinite.exists_notMem_finset (insert ab.1.1 (insert ab.2.1 p.support))
      have hs : n ∉ p.support := by simpa using fun h => hn (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem h))
      have ha : ab.1.1 ≠ n := fun h => hn (h ▸ Finset.mem_insert_self _ _)
      have hb : ab.2.1 ≠ n := fun h => hn (Finset.mem_insert_of_mem
        (h ▸ Finset.mem_insert_self _ _))
      exact ⟨p.insert ab.1 ab.2 n hs ha hb hab missing,
        Partial.le_insert p ab.1 ab.2 n hs ha hb hab missing,
        Or.inr ⟨_,Partial.insert_covers p ab.1 ab.2 n hs ha hb hab missing⟩⟩) Partial.empty
  let R := fun a b c => ∃ p ∈ chain, p.R a b c
  refine ⟨⟨R,?_,?_,?_,?_,?_,?_⟩⟩
  · rintro a b c d ⟨p,hp,hc⟩ ⟨q,hq,hd⟩
    rcases eq_or_ne p q with rfl | hne
    · exact p.functional _ _ _ _ hc hd
    rcases hchain hp hq hne with hpq | hqp
    · exact q.functional _ _ _ _ (hpq _ _ _ hc) hd
    · exact p.functional _ _ _ _ hc (hqp _ _ _ hd)
  · rintro a b c ⟨p,hp,h⟩
    exact ⟨p,hp,p.rotate _ _ _ h⟩
  · rintro a b c ⟨p,hp,h⟩ k
    exact ⟨p,hp,p.translate _ _ _ h k⟩
  · rintro a b c ⟨p,_,h⟩
    exact p.avoid _ _ _ h
  · rintro a b c ⟨p,_,h⟩
    exact p.lower _ _ _ h
  · intro a b hab
    obtain ⟨p,hp,h⟩ := hcover (a,b)
    rcases h with h | ⟨c,hc⟩
    · exact False.elim (hab h)
    · exact ⟨c,p,hp,hc⟩

def complete : Completed := Classical.choice exists_completed

end
end Parastrophes.TwistedCycleCompletion
