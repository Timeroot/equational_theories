import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic

/-!
# Endpoint constraints preventing free-group cancellation

A cone is specified by a set of generator indices: both endpoints use an
index in that set, and the last letter is positive. The first letter may
have either sign. Keeping the index 0 apart from the positive indices gives
a convenient invariant for the noncommutative E1719 triangle trades.
-/
namespace Parastrophes.FreeGroupWordCones
open FreeGroup
abbrev Word := FreeGroup Nat
abbrev Letter := Nat × Bool

def Cone (P : Nat → Prop) (x : Word) : Prop :=
  (∃ i b, P i ∧ x.toWord.head? = some (i,b)) ∧
  ∃ j, P j ∧ x.toWord.getLast? = some (j,true)

def Fresh (k : Nat) (x : Word) : Prop := ∀ e ∈ x.toWord, e.1 ≠ k

/-- Multiplication concatenates the reduced words if the two boundary
letters cannot be inverse to one another. -/
theorem join {x y : Word} {a b : Letter}
    (hx : x.toWord.getLast? = some a) (hy : y.toWord.head? = some b)
    (h : a.1 = b.1 → a.2 = b.2) :
    (x*y).toWord = x.toWord ++ y.toWord := by
  rw [FreeGroup.toWord_mul]
  apply FreeGroup.IsReduced.reduce_eq
  apply List.IsChain.append FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
  intro c hc d hd hcd
  rw [hx] at hc
  rw [hy] at hd
  have hc' : a=c := by simpa only [Option.mem_some_iff] using hc
  have hd' : b=d := by simpa only [Option.mem_some_iff] using hd
  subst c
  subst d
  exact h hcd

theorem join_ends {x y : Word} {a b c d : Letter}
    (hxa : x.toWord.head? = some a) (hxb : x.toWord.getLast? = some b)
    (hyc : y.toWord.head? = some c) (hyd : y.toWord.getLast? = some d)
    (h : b.1 = c.1 → b.2 = c.2) :
    (x*y).toWord.head? = some a ∧ (x*y).toWord.getLast? = some d := by
  have hxn : x.toWord ≠ [] := by intro he; simp [he] at hxa
  have hyn : y.toWord ≠ [] := by intro he; simp [he] at hyd
  rw [join hxb hyc h]
  exact ⟨by rw [List.head?_append_of_ne_nil _ hxn]; exact hxa,
    by rw [List.getLast?_append_of_ne_nil _ hyn]; exact hyd⟩

theorem inv_head {x : Word} {i : Nat} {b : Bool}
    (h : x.toWord.getLast? = some (i,b)) : x⁻¹.toWord.head? = some (i,!b) := by
  simp [FreeGroup.toWord_inv, FreeGroup.invRev, List.head?_reverse, h]

theorem inv_last {x : Word} {i : Nat} {b : Bool}
    (h : x.toWord.head? = some (i,b)) : x⁻¹.toWord.getLast? = some (i,!b) := by
  simp [FreeGroup.toWord_inv, FreeGroup.invRev, List.getLast?_reverse, h]

theorem fresh_head {x : Word} {k i : Nat} {b : Bool}
    (hf : Fresh k x) (h : x.toWord.head? = some (i,b)) : i ≠ k := by
  exact hf (i,b) (List.mem_of_mem_head? h)

theorem fresh_last {x : Word} {k i : Nat} {b : Bool}
    (hf : Fresh k x) (h : x.toWord.getLast? = some (i,b)) : i ≠ k := by
  exact hf (i,b) (List.mem_of_mem_getLast? h)

theorem generator_cone {P : Nat → Prop} {i : Nat} (hi : P i) : Cone P (FreeGroup.of i) :=
  ⟨⟨i,true,hi,by simp⟩,⟨i,hi,by simp⟩⟩

abbrev ZeroCone := Cone (· = 0)
abbrev PositiveCone := Cone (0 < ·)

/-- The first coordinate of a designated left product has no cancellation,
so it strictly increases in length and remains in the zero-index cone. -/
theorem first_product {a u : Word} {k : Nat}
    (ha : ZeroCone a) (hu : ZeroCone u) (hk : 0 < k) :
    ZeroCone (u⁻¹ * FreeGroup.of k * a) ∧
    (u⁻¹ * FreeGroup.of k * a).toWord.length = u.toWord.length + 1 + a.toWord.length := by
  obtain ⟨⟨_,ba,rfl,hah⟩,⟨_,rfl,hal⟩⟩ := ha
  obtain ⟨⟨_,bu,rfl,huh⟩,⟨_,rfl,hul⟩⟩ := hu
  have hiH := inv_head hul
  have hiL := inv_last huh
  have hgH : (FreeGroup.of k).toWord.head? = some (k,true) := by simp
  have hgL : (FreeGroup.of k).toWord.getLast? = some (k,true) := by simp
  have h1 : (0 : Nat) = k → (!bu) = true := by omega
  have h2 : k = (0 : Nat) → true = ba := by omega
  have hw1 := join hiL hgH h1
  have he1 := join_ends hiH hiL hgH hgL h1
  have hw2 := join he1.2 hah h2
  have he2 := join_ends he1.1 he1.2 hah hal h2
  refine ⟨⟨⟨0,false,rfl,by simpa using he2.1⟩,⟨0,rfl,he2.2⟩⟩,?_⟩
  rw [hw2,hw1,FreeGroup.toWord_inv]
  simp only [List.length_append,FreeGroup.invRev_length,FreeGroup.toWord_of,List.length_singleton]

/-- The second coordinate stays among positive endpoint indices. Freshness
is only needed at the final boundary next to the chosen generator. -/
theorem second_product {a b v : Word} {k : Nat}
    (ha : ZeroCone a) (hb : PositiveCone b) (hv : PositiveCone v)
    (hk : 0 < k) (hf : Fresh k b) :
    PositiveCone (v⁻¹ * a⁻¹ * b⁻¹ * FreeGroup.of k) := by
  obtain ⟨⟨_,ba,rfl,hah⟩,⟨_,rfl,hal⟩⟩ := ha
  obtain ⟨⟨ib,bb,hib,hbh⟩,⟨jb,hjb,hbl⟩⟩ := hb
  obtain ⟨⟨iv,bv,hiv,hvh⟩,⟨jv,hjv,hvl⟩⟩ := hv
  have h1 := join_ends (inv_head hvl) (inv_last hvh) (inv_head hal) (inv_last hah)
    (show iv=0 → (!bv)=(!true) by omega)
  have h2 := join_ends h1.1 h1.2 (inv_head hbl) (inv_last hbh)
    (show 0=jb → (!ba)=(!true) by omega)
  have h3 := join_ends h2.1 h2.2
    (show (FreeGroup.of k).toWord.head? = some (k,true) by simp)
    (show (FreeGroup.of k).toWord.getLast? = some (k,true) by simp)
    (fun h => False.elim (fresh_head hf hbh h))
  exact ⟨⟨jv,false,hjv,by simpa using h3.1⟩,⟨k,hk,h3.2⟩⟩

end Parastrophes.FreeGroupWordCones
