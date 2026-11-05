import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Tactic

/-!
# Boolean simulation in partial E115 turns

This is the combinatorial part of the finite-image obstruction described in
`docs/e115-finite-right-image.md`. A productive and a reserved family of fresh
coordinates let us preserve Boolean NOT-left-AND-right on nonnegative points.
The finite transfer and the final negative theorem are in
`Equation115FiniteImageObstruction.lean`.
-/
namespace Parastrophes.Eq115BooleanTurn
noncomputable section

abbrev W := ℤ × ((ℕ →₀ ℤ) × (ℕ →₀ ℤ))
def s : W := (1,0,0)
def height (x : W) : ℤ := x.1
def reserved (x : W) : ℕ →₀ ℤ := x.2.2

@[simp] theorem height_add (x y : W) : height (x+y)=height x+height y := rfl
@[simp] theorem height_sub (x y : W) : height (x-y)=height x-height y := rfl
@[simp] theorem height_neg (x : W) : height (-x) = -height x := rfl
@[simp] theorem height_s : height s=1 := rfl
@[simp] theorem height_zero : height (0 : W)=0 := rfl
@[simp] theorem reserved_add (x y : W) : reserved (x+y)=reserved x+reserved y := rfl
@[simp] theorem reserved_sub (x y : W) : reserved (x-y)=reserved x-reserved y := rfl
@[simp] theorem reserved_neg (x : W) : reserved (-x) = -reserved x := rfl
@[simp] theorem reserved_s : reserved s=0 := rfl
@[simp] theorem reserved_zero : reserved (0 : W)=0 := rfl

def Good (x y : W) : Prop :=
  (0 < height x → height y=0 ∧ reserved y=0) ∧
  (height x < 0 → 0 ≤ height y ∧ height y < -height x) ∧
  (height x=0 → height y ≤ 0) ∧
  (height x=0 → reserved x=0 → height y < 0)

def Positive (x : W) : Prop := 0 ≤ height x ∧ (height x=0 → reserved x=0)

def color (x : W) : Bool := decide (height x=0)

/-- The sign conditions give the desired Boolean operation. The strict
zero-height clause is precisely why reserved fresh coordinates are needed. -/
theorem simulate {x y t : W} (hx : Positive x) (hy : Positive y)
    (ht : Good (x-y) t) :
    Positive (y-t) ∧ color (y-t) = (!color x && color y) := by
  have hx0 := hx.1
  have hy0 := hy.1
  unfold Good at ht
  simp only [height_sub, reserved_sub] at ht
  rcases lt_trichotomy (height x) (height y) with h | h | h
  · obtain ⟨ht0,ht1⟩ := ht.2.1 (by omega)
    have hp : 0 < height (y-t) := by simp only [height_sub]; omega
    have hy0 : height y ≠ 0 := by omega
    refine ⟨⟨by omega, fun hz => by omega⟩, ?_⟩
    unfold color
    simp only [decide_eq_false (ne_of_gt hp), decide_eq_false hy0, Bool.and_false]
  · by_cases hz : height x=0
    · have hyz : height y=0 := by omega
      have ht0 := ht.2.2.2 (by omega) (by rw [hx.2 hz, hy.2 hyz, sub_self])
      have hp : 0 < height (y-t) := by simp only [height_sub]; omega
      refine ⟨⟨by omega, fun he => by omega⟩, ?_⟩
      unfold color
      simp only [decide_eq_false (ne_of_gt hp), decide_eq_true hz, decide_eq_true hyz]
      rfl
    · have ht0 := ht.2.2.1 (by omega)
      have hp : 0 < height (y-t) := by simp only [height_sub]; omega
      refine ⟨⟨by omega, fun he => by omega⟩, ?_⟩
      unfold color
      have hyz : height y ≠ 0 := by omega
      simp only [decide_eq_false (ne_of_gt hp), decide_eq_false hz, decide_eq_false hyz]
      rfl
  · obtain ⟨ht0,htr⟩ := ht.1 (by omega)
    have he : height (y-t)=height y := by simp [ht0]
    have hx0 : height x ≠ 0 := by omega
    refine ⟨⟨by rw [he]; exact hy.1, ?_⟩, ?_⟩
    · intro hh
      rw [reserved_sub, htr, hy.2 (he ▸ hh), sub_self]
    · simp [color, he, hx0]

/-- A triangle, including its orientation. -/
def Cycle (a b c x y : W) : Prop :=
  (x=a ∧ y=b) ∨ (x=b ∧ y=c) ∨ (x=c ∧ y=a)

structure Partial where
  R : W → W → Prop
  functional : ∀ x y z, R x y → R x z → y=z
  rotate : ∀ x y, R x y → R y (-s-x-y)
  good : ∀ x y, R x y → Good x y
  support : Finset W
  supported : ∀ x y, R x y → x ∈ support ∧ y ∈ support

namespace Partial
instance : Preorder Partial where
  le p q := ∀ x y, p.R x y → q.R x y
  le_refl _ := fun _ _ h => h
  le_trans _ _ _ hp hq := fun _ _ h => hq _ _ (hp _ _ h)

private theorem cycle_functional {a b c : W} (hab : a≠b) (hbc : b≠c) (hac : a≠c)
    {x y z} (h : Cycle a b c x y) (h' : Cycle a b c x z) : y=z := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rcases h' with ⟨he,rfl⟩ | ⟨he,rfl⟩ | ⟨he,rfl⟩
  all_goals aesop

private theorem cycle_rotate {a b c x y : W} (hs : a+b+c = -s)
    (h : Cycle a b c x y) : Cycle a b c y (-s-x-y) := by
  rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · rw [hx,hy]
    right; left; constructor; rfl
    calc
      -s-a-b = (a+b+c)-a-b := by rw [hs]
      _ = c := by abel
  · rw [hx,hy]
    right; right; constructor; rfl
    calc
      -s-b-c = (a+b+c)-b-c := by rw [hs]
      _ = a := by abel
  · rw [hx,hy]
    left; constructor; rfl
    calc
      -s-c-a = (a+b+c)-c-a := by rw [hs]
      _ = b := by abel

def seed : Partial where
  R := Cycle 0 (-s-s) s
  functional := by
    apply cycle_functional
    all_goals intro he; have hh := congrArg height he; norm_num at hh
  rotate := by
    intro x y h
    exact cycle_rotate (by abel) h
  good := by
    intro x y h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [Good]
  support := {0,-s-s,s}
  supported := by
    intro x y h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

/-- Add one new oriented triangle, checking geometric and sign invariants
separately. Existing turn values are never changed. -/
def insert (p : Partial) (a b c : W)
    (hab : a≠b) (hbc : b≠c) (hac : a≠c)
    (ha : ∀ y, ¬ p.R a y) (hb : b ∉ p.support) (hc : c ∉ p.support)
    (hs : a+b+c = -s) (gab : Good a b) (gbc : Good b c) (gca : Good c a) : Partial where
  R := fun x y => p.R x y ∨ Cycle a b c x y
  functional := by
    intro x y z hy hz
    have disjoint {x y z} (ho : p.R x y) (hn : Cycle a b c x z) : False := by
      rcases hn with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact ha _ ho
      · exact hb (p.supported _ _ ho).1
      · exact hc (p.supported _ _ ho).1
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · exact p.functional _ _ _ hy hz
    · exact False.elim (disjoint hy hz)
    · exact False.elim (disjoint hz hy)
    · exact cycle_functional hab hbc hac hy hz
  rotate := by
    intro x y h
    exact h.elim (fun h => Or.inl (p.rotate _ _ h)) (fun h => Or.inr (cycle_rotate hs h))
  good := by
    intro x y h
    rcases h with h | h
    · exact p.good _ _ h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact gab
    · exact gbc
    · exact gca
  support := p.support ∪ {a,b,c}
  supported := by
    intro x y h
    rcases h with h | h
    · exact ⟨Finset.mem_union_left _ (p.supported _ _ h).1,
        Finset.mem_union_left _ (p.supported _ _ h).2⟩
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

private def extra (x : W) : Finset ℕ := x.2.1.support ∪ x.2.2.support

private theorem zero_extra {x : W} {k : ℕ} (hk : k ∉ extra x) :
    x.2.1 k=0 ∧ x.2.2 k=0 := by
  simpa only [extra, Finset.mem_union, not_or, Finsupp.notMem_support_iff] using hk

/-- A fresh productive coordinate handles nonzero heights other than -1;
a reserved coordinate handles the two exceptional heights 0 and -1. -/
theorem extend (p : Partial) (a : W) : ∃ q : Partial, p ≤ q ∧ ∃ b, q.R a b := by
  classical
  by_cases hex : ∃ b, p.R a b
  · exact ⟨p, le_rfl, hex⟩
  have ha : ∀ b, ¬ p.R a b := by simpa using hex
  obtain ⟨k,hk⟩ := Infinite.exists_notMem_finset
    (extra a ∪ p.support.biUnion extra)
  have hka : a.2.1 k=0 ∧ a.2.2 k=0 := zero_extra (fun h => hk (Finset.mem_union_left _ h))
  have hkp (x) (hx : x ∈ p.support) : x.2.1 k=0 ∧ x.2.2 k=0 := by
    apply zero_extra
    intro h
    exact hk (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,h⟩))
  let productive := 0 < height a ∨ height a < -1
  let e : W := if productive then (0,Finsupp.single k 1,0) else (0,0,Finsupp.single k 1)
  let b : W := -s-a-e
  let coord : W → ℤ := fun x => if productive then x.2.1 k else x.2.2 k
  have ca : coord a=0 := by simp only [coord]; split <;> simp [hka]
  have ce : coord e=1 := by by_cases h : productive <;> simp [coord,e,h]
  have cb : coord b= -1 := by
    by_cases h : productive <;> simp [coord,b,e,s,h,hka]
  have cp (x) (hx : x ∈ p.support) : coord x=0 := by
    simp only [coord]; split <;> simp [(hkp x hx).1,(hkp x hx).2]
  have hae : a≠e := by intro h; have hh := congrArg coord h; omega
  have hab : a≠b := by intro h; have hh := congrArg coord h; omega
  have heb : e≠b := by intro h; have hh := congrArg coord h; omega
  have he : e ∉ p.support := by intro h; have hh := cp e h; omega
  have hb : b ∉ p.support := by intro h; have hh := cp b h; omega
  have hes : height e=0 := by by_cases h : productive <;> simp [e,h,height]
  have hbs : height b= -1-height a := by simp [b,hes]
  by_cases hp : 0 < height a
  · have he0 : reserved e=0 := by simp [e,productive,hp,reserved]
    have gab : Good a e := by simp [Good,hes,he0]; omega
    have gbc : Good e b := by simp only [Good,hes,hbs]; omega
    have gca : Good b a := by simp only [Good,hbs]; omega
    let q := p.insert a e b hae heb hab ha he hb (by dsimp [b]; abel) gab gbc gca
    exact ⟨q,fun _ _ h => Or.inl h,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  · have hs : a+b+e= -s := by dsimp [b]; abel
    have gab : Good a b := by
      simp only [Good,hbs]
      omega
    have gca : Good e a := by
      by_cases hn : height a < -1
      · simp only [Good,hes]; omega
      · have he1 : reserved e k=1 := by simp [e,productive,hp,hn,reserved]
        have her : reserved e ≠ 0 := by intro h; simp [h] at he1
        simp [Good,hes,her]; omega
    have gbc : Good b e := by
      by_cases hn : height a < -1
      · have he0 : reserved e=0 := by simp [e,productive,hn,reserved]
        simp [Good,hbs,hes,he0]; omega
      · have hb1 : reserved b k= -1 := by
          simp [b,e,productive,hp,hn,reserved,s,hka]
        have hbr : reserved b ≠ 0 := by intro h; simp [h] at hb1
        simp [Good,hbs,hes,hbr]; omega
    let q := p.insert a b e hab heb.symm hae ha hb he hs gab gbc gca
    exact ⟨q,fun _ _ h => Or.inl h,b,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩

end Partial
/-- A total turn with the seed and the Boolean sign invariants. -/
structure Completed where
  turn : W → W
  cube : ∀ x, turn (turn (turn x))=x
  sum : ∀ x, x + turn x + turn (turn x) = -s
  good : ∀ x, Good x (turn x)
  zero : turn 0 = -s-s
  second : turn (-s-s)=s

/-- Each task defines the turn at one point. The union of the resulting
chain is total and retains every three-cycle already installed. -/
theorem exists_completed : Nonempty Completed := by
  classical
  obtain ⟨chain,hchain,hseed,_,hcover⟩ := exists_greedy_chain
    (fun a : W => {p : Partial | ∃ b, p.R a b}) Partial.extend Partial.seed
  let R := fun a b => ∃ p ∈ chain, p.R a b
  have functional (a b c) (hb : R a b) (hc : R a c) : b=c := by
    obtain ⟨p,hp,hb⟩ := hb
    obtain ⟨q,hq,hc⟩ := hc
    rcases eq_or_ne p q with rfl | hne
    · exact p.functional _ _ _ hb hc
    rcases hchain hp hq hne with h | h
    · exact q.functional _ _ _ (h _ _ hb) hc
    · exact p.functional _ _ _ hb (h _ _ hc)
  have total (a) : ∃ b, R a b := by
    obtain ⟨p,hp,b,hb⟩ := hcover a
    exact ⟨b,p,hp,hb⟩
  let t := fun a => Classical.choose (total a)
  have ht (a) : R a (t a) := Classical.choose_spec (total a)
  have hr (a b) (h : R a b) : R b (-s-a-b) := by
    obtain ⟨p,hp,h⟩ := h
    exact ⟨p,hp,p.rotate _ _ h⟩
  have he (a) : t (t a)= -s-a-t a := functional _ _ _ (ht _) (hr _ _ (ht a))
  refine ⟨⟨t,?_,?_,?_,?_,?_⟩⟩
  · intro a
    rw [he (t a), he a]
    abel
  · intro a
    rw [he]
    abel
  · intro a
    obtain ⟨p,_,h⟩ := ht a
    exact p.good _ _ h
  · exact functional _ _ _ (ht 0) ⟨Partial.seed,hseed,Or.inl ⟨rfl,rfl⟩⟩
  · exact functional _ _ _ (ht (-s-s)) ⟨Partial.seed,hseed,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩

end
end Parastrophes.Eq115BooleanTurn
