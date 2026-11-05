import equational_theories.Parastrophes.FiniteTriangleBasis
import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All

/-!
# No single identity for E1719's finite right-division image

For every finite term, we construct an actual finite division image in which
all variables have value e₀ and each composite subterm becomes a basis
vector whose index exceeds both input indices. The model is on
(F5)^N × (F5)^N. Its turn s is obtained from
the finite triangle trades, and its operations are

    M(x,y) = -s²(x)-y,           R(x,y) = s(-y-x).

The zero-sum and order-three properties of s prove E1719 for M and prove
that R is its right division. The triples indexed by unordered pairs i,j
force R(e_i,e_j)=e_(pair(min i j,max i j)+1).

Consequently no identity `variable = composite term` holds in every finite
image. An identity with two composite sides, or a tautological variable
identity, also holds in the two-element constant magma, which has no right
division. Distinct-variable identities fail in a nontrivial finite image.
These alternatives exhaust all possible single identities, of any length.
-/
namespace Parastrophes.Eq1719FiniteRightImage
open Law FreeMagma FiniteTriangleBasis

def node (i j : Nat) := Nat.pair (min i j) (max i j) + 1

theorem node_comm (i j) : node i j = node j i := by simp [node, min_comm, max_comm]

theorem lt_node_left (i j) : i < node i j := by
  have h := Nat.right_le_pair (min i j) (max i j)
  have hi := Nat.le_max_left i j
  unfold node
  omega

theorem lt_node_right (i j) : j < node i j := by
  rw [node_comm]
  exact lt_node_left j i

def code : FreeMagma Nat → Nat
  | .Leaf _ => 0
  | .Fork a b => node (code a) (code b)

abbrev Carrier (n : Nat) := Vec n × Vec n

private theorem turn_exists (n : Nat) : ∃ s : Carrier n → Carrier n,
    (∀ x, s (s (s x)) = x) ∧ (∀ x, x + s (s x) + s x = 0) ∧
    (∀ p : Block n, s (negative p, 0) = (basis (output p),0)) := by
  obtain ⟨s,hc,hs,ht⟩ := FiniteTriangleTrades.exists_turn (@triple n)
    triple_injective triple_nonzero triple_sum
  exact ⟨s,hc,hs,fun p => by simpa [triple] using ht p⟩

noncomputable def turn (n : Nat) := Classical.choose (turn_exists n)

theorem turn_cube (n) (x : Carrier n) : turn n (turn n (turn n x)) = x :=
  (Classical.choose_spec (turn_exists n)).1 x

theorem turn_sum (n) (x : Carrier n) : x + turn n (turn n x) + turn n x = 0 :=
  (Classical.choose_spec (turn_exists n)).2.1 x

theorem turn_block {n} (p : Block n) :
    turn n (negative p,0) = (basis (output p),0) :=
  (Classical.choose_spec (turn_exists n)).2.2 p

@[implicit_reducible] noncomputable def source (n : Nat) : Magma (Carrier n) :=
  ⟨fun x y => -turn n (turn n x)-y⟩

@[implicit_reducible] noncomputable def right (n : Nat) : Magma (Carrier n) :=
  ⟨fun x y => turn n (-y-x)⟩

theorem square_source (n) (x : Carrier n) : (source n).op x x = turn n x := by
  change -turn n (turn n x)-x = turn n x
  calc
    _ = (-turn n (turn n x)-x) + (x+turn n (turn n x)+turn n x) := by
      rw [turn_sum, add_zero]
    _ = turn n x := by abel

theorem source_law (n) : @Equation1719 (Carrier n) (source n) := by
  intro x y
  rw [square_source, square_source]
  change x = -turn n (turn n (turn n y)) - (-turn n (turn n (turn n x))-y)
  rw [turn_cube, turn_cube]
  abel

theorem isDivision (n) : IsDivision .right (source n) (right n) := by
  constructor <;> intro x y
  · change -turn n (turn n (turn n (-y-x)))-y = x
    rw [turn_cube]
    abel
  · change turn n (-y-(-turn n (turn n x)-y)) = x
    rw [show -y-(-turn n (turn n x)-y) = turn n (turn n x) by abel]
    exact turn_cube n x

theorem inImage (n) : InImage Law1719 .right (right n) :=
  ⟨source n, (@Law1719.models_iff (Carrier n) (source n)).mpr (source_law n), isDivision n⟩

theorem right_comm (n) (x y : Carrier n) : (right n).op x y = (right n).op y x := by
  change turn n (-y-x) = turn n (-x-y)
  congr 1
  abel

theorem right_basis_ordered {n} (i j : Fin n) (hij : i ≤ j) (hn : node i.val j.val < n) :
    (right n).op (basis i,0) (basis j,0) = (basis ⟨node i.val j.val,hn⟩,0) := by
  have hv : i.val ≤ j.val := hij
  let p : Block n := ⟨(i,j), ⟨hij, by simpa [node, min_eq_left hv, max_eq_right hv] using hn⟩⟩
  have ho : output p = ⟨node i.val j.val,hn⟩ := by
    apply Fin.ext
    simp [output, p, node, min_eq_left hv, max_eq_right hv]
  calc
    _ = turn n (negative p,0) := by
      change turn n (-(basis j,0)-(basis i,0)) = turn n (-basis i-basis j,0)
      congr 1
      apply Prod.ext <;> simp
      abel
    _ = (basis (output p),0) := turn_block p
    _ = _ := by rw [ho]

theorem right_basis {n} (i j : Fin n) (hn : node i.val j.val < n) :
    (right n).op (basis i,0) (basis j,0) = (basis ⟨node i.val j.val,hn⟩,0) := by
  rcases le_total i j with h | h
  · exact right_basis_ordered i j h hn
  · rw [right_comm]
    have he := node_comm j.val i.val
    have hn' : node j.val i.val < n := by rwa [he]
    simpa only [he] using right_basis_ordered j i h hn'

theorem eval_code {n} (hn : 0 < n) (t : FreeMagma Nat) (ht : code t < n) :
    @evalInMagma _ _ (right n) (fun _ => (basis ⟨0,hn⟩,0)) t = (basis ⟨code t,ht⟩,0) := by
  induction t with
  | Leaf i => rfl
  | Fork a b ha hb =>
    have hta : code a < n := lt_trans (lt_node_left _ _) ht
    have htb : code b < n := lt_trans (lt_node_right _ _) ht
    change (right n).op (@evalInMagma _ _ (right n) _ a)
      (@evalInMagma _ _ (right n) _ b) = _
    rw [ha hta, hb htb]
    exact right_basis _ _ ht

/-- An arbitrary composite term fails to return its common input in an actual
finite right-division image. The dimension depends on the term; no bounded
table search or uniform upper bound on term size is used. -/
theorem refute_fork (a b : FreeMagma Nat) :
    ∃ (G : Type) (_ : Finite G) (D : Magma G) (e : G),
      InImage Law1719 .right D ∧ @evalInMagma _ _ D (fun _ => e) (a ⋆ b) ≠ e := by
  let n := code (a ⋆ b) + 1
  have hn : 0 < n := Nat.succ_pos _
  have ht : code (a ⋆ b) < n := Nat.lt_succ_self _
  refine ⟨Carrier n, inferInstance, right n, (basis ⟨0,hn⟩,0), inImage n, ?_⟩
  rw [eval_code hn _ ht]
  intro he
  have hi := basis_injective (congrArg Prod.fst he)
  have hv := congrArg Fin.val hi
  have hp := lt_node_left (code a) (code b)
  change node (code a) (code b) = 0 at hv
  omega

@[implicit_reducible] private def constant : Magma Bool := ⟨fun _ _ => false⟩

private theorem constant_not_image : ¬ InImage Law1719 .right constant := by
  rintro ⟨M,_,hd⟩
  have hh := hd.2 true false
  exact Bool.noConfusion hh

/-- The finite right image is not characterized by any single magma identity,
regardless of the number of variables or operation symbols. -/
theorem no_singleEquation : ¬ SingleEquation .fin Law1719 .right := by
  rintro ⟨⟨l,r⟩,hc⟩
  cases l with
  | Leaf i =>
    cases r with
    | Leaf j =>
      by_cases hij : i=j
      · subst j
        apply constant_not_image
        exact (hc Bool constant (inferInstance : Finite Bool)).1 (fun _ => rfl)
      · obtain ⟨G,hG,D,e,hi,hn⟩ := refute_fork (Lf 0) (Lf 0)
        let q := @evalInMagma _ _ D (fun _ => e) ((Lf 0) ⋆ (Lf 0))
        have he := (hc G D hG).2 hi (fun k => if k=i then e else q)
        change (if i=i then e else q) = (if j=i then e else q) at he
        have hji : j ≠ i := fun h => hij h.symm
        have he' : e=q := by simpa only [ite_true, if_neg hji] using he
        exact hn he'.symm
    | Fork a b =>
      obtain ⟨G,hG,D,e,hi,hn⟩ := refute_fork a b
      exact hn ((hc G D hG).2 hi (fun _ => e)).symm
  | Fork a b =>
    cases r with
    | Leaf i =>
      obtain ⟨G,hG,D,e,hi,hn⟩ := refute_fork a b
      exact hn ((hc G D hG).2 hi (fun _ => e))
    | Fork c d =>
      apply constant_not_image
      exact (hc Bool constant (inferInstance : Finite Bool)).1 (fun _ => rfl)

end Parastrophes.Eq1719FiniteRightImage

namespace Parastrophes.Catalogue

/-- Finite triangle trades refute every variable-to-composite identity in the
right image; identities with two composite sides cannot exclude constants. -/
@[parastrophe_result] theorem right_noSingleEquation1719_fin :
    ¬ SingleEquation .fin Law1719 .right := Eq1719FiniteRightImage.no_singleEquation

end Parastrophes.Catalogue
