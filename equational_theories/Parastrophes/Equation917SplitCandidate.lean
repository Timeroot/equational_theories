import equational_theories.Parastrophes.Equation917SingleCandidate

/-!
# Independent auxiliary variables in an E917 compression

This records valid consequences of a refuted candidate, not a characterization. Write
F(x,z)=z*(c(x)*(x*z)), where c(x)=(x*(x*x))*x. The new 22-operation candidate
is x=y*(K(x,z,w)*(x*y)), with

    B(x,z,w)=F(z,w)*(c(x)*(x*z)),
    K(x,z,w)=((B(x,z,w)*c(x))*(x*x))*x.

Keeping w independent of z is essential to the argument below. It forces
F(z,w) to be a common g(z), and B(x,z,w) to be a common h(x). These maps
are permutations, and h=f∘g where m(g(x),y)=f(m(x,y)). The converse is FALSE:
`Equation917SplitCounterexample.lean` proves that `43*x+17*y+1` on Z/59Z
satisfies the candidate but fails the unit law. No attribute is attached.
-/
namespace Parastrophes.Eq917Image.SplitCandidate

variable {G : Type} (D : Magma G)

def F (x z : G) := D.op z (D.op (core D x) (D.op x z))
def B (x z w : G) := D.op (F D z w) (D.op (core D x) (D.op x z))
def K (x z w : G) := D.op (D.op (D.op (B D x z w) (core D x)) (D.op x x)) x
def Identity : Prop := ∀ x y z w, x = D.op y (D.op (K D x z w) (D.op x y))

theorem of_basis (h : Basis D) : Identity D := by
  have hf (x z : G) : F D x z = x := (h.2 x z).symm
  have hb (x z w : G) : B D x z w = x := by
    simp only [B, hf]
    exact (h.2 x z).symm
  have hu (x : G) : D.op x (core D x) = x := (h.1 x).symm
  have hk (x z w : G) : K D x z w = core D x := by
    simp only [K, hb, hu]
    rfl
  intro x y z w
  rw [hk]
  exact h.2 x y

theorem quasigroup [Finite G] (h : Identity D) : IsQuasigroup D :=
  Candidate.quasigroup_of_frame D (fun x z => K D x z x) (fun x y z => h x y z x)

theorem B_independent [Finite G] (h : Identity D) (x z w z' w' : G) :
    B D x z w = B D x z' w' := by
  have hq := quasigroup D h
  have hk : K D x z w = K D x z' w' := by
    apply (hq.2 (D.op x x)).1
    apply (hq.1 x).1
    exact (h x x z w).symm.trans (h x x z' w')
  exact (hq.2 (core D x)).1 ((hq.2 (D.op x x)).1 ((hq.2 x).1 hk))

theorem F_independent [Finite G] (h : Identity D) (z w w' : G) :
    F D z w = F D z w' := by
  apply ((quasigroup D h).2 (D.op (core D z) (D.op z z))).1
  exact B_independent D h z z w z w'

/-- The reusable finite permutation argument. No assertion that these
permutations are trivial is included; the rest of the candidate is still needed. -/
theorem common_permutations [Finite G] (c g h : G → G) (hq : IsQuasigroup D)
    (hF : ∀ x y, D.op y (D.op (c x) (D.op x y)) = g x)
    (hH : ∀ x y, D.op (g y) (D.op (c x) (D.op x y)) = h x) :
    ∃ f : G → G, Function.Bijective g ∧ Function.Bijective f ∧
      (∀ x, h x = f (g x)) ∧ (∀ x y, D.op (g x) y = f (D.op x y)) := by
  have hg : Function.Injective g := by
    intro a b he
    apply (hq.1 a).1
    apply (hq.1 (c a)).1
    apply (hq.1 (g a)).1
    calc
      _ = h a := hH a a
      _ = D.op (g b) (D.op (c a) (D.op a b)) := (hH a b).symm
      _ = _ := by rw [he]
  have hgb : Function.Bijective g := ⟨hg, Finite.injective_iff_surjective.mp hg⟩
  let e : G ≃ G := Equiv.ofBijective g hgb
  let f := fun t => h (e.symm t)
  have ha (x y : G) : D.op (g x) y = f (D.op x y) := by
    let t := e.symm (D.op x y)
    have ht : g t = D.op x y := e.apply_symm_apply _
    have hi : D.op (c t) (D.op t x) = y := (hq.1 x).1 ((hF t x).trans ht)
    calc
      _ = D.op (g x) (D.op (c t) (D.op t x)) := by rw [hi]
      _ = h t := hH t x
      _ = _ := rfl
  have hf : Function.Injective f := by
    intro a b he
    obtain ⟨a', ha'⟩ := (hq.1 a).2 a
    obtain ⟨b', hb'⟩ := (hq.1 a).2 b
    have hh : D.op (g a) a' = D.op (g a) b' := by rw [ha, ha, ha', hb']; exact he
    have hh' := (hq.1 (g a)).1 hh
    exact ha'.symm.trans ((congrArg (D.op a) hh').trans hb')
  refine ⟨f, hgb, ⟨hf, Finite.injective_iff_surjective.mp hf⟩, ?_, ha⟩
  intro x
  change h x = h (e.symm (e x))
  rw [e.symm_apply_apply]

/-- A left-index/output autotopy of a quasigroup is determined by its value
at one point. This is an arbitrary-carrier statement, not a finite search. -/
theorem autotopy_fixed_point (g f : G → G) (hq : IsQuasigroup D)
    (ha : ∀ x y, D.op (g x) y = f (D.op x y))
    (a : G) (hga : g a = a) : (∀ x, g x = x) ∧ (∀ x, f x = x) := by
  have hf (x : G) : f x = x := by
    obtain ⟨y, rfl⟩ := (hq.1 a).2 x
    exact (ha a y).symm.trans (by rw [hga])
  refine ⟨?_, hf⟩
  intro x
  exact (hq.2 a).1 ((ha x a).trans (hf _))

/-- A fixed point of the output map also trivializes both maps. -/
theorem output_fixed_point (g f : G → G) (hq : IsQuasigroup D)
    (ha : ∀ x y, D.op (g x) y = f (D.op x y))
    (a : G) (hfa : f a = a) : (∀ x, g x = x) ∧ (∀ x, f x = x) := by
  obtain ⟨y, hy⟩ := (hq.1 a).2 a
  have hg : g a = a := (hq.2 y).1 (by
    change D.op (g a) y = D.op a y
    rw [ha, hy, hfa])
  exact autotopy_fixed_point D g f hq ha a hg

/-- Corresponding powers are again an autotopy. -/
theorem autotopy_iterate (g f : G → G)
    (ha : ∀ x y, D.op (g x) y = f (D.op x y)) (n : ℕ) (x y : G) :
    D.op ((g^[n]) x) y = (f^[n]) (D.op x y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ha, ih]

/-- In particular, if a power fixes one point, that power is the identity
on the entire carrier. Nontrivial finite cycles therefore all have one length. -/
theorem iterate_fixed_point (g f : G → G) (hq : IsQuasigroup D)
    (ha : ∀ x y, D.op (g x) y = f (D.op x y))
    (n : ℕ) (a : G) (hn : (g^[n]) a = a) :
    (∀ x, (g^[n]) x = x) ∧ (∀ x, (f^[n]) x = x) :=
  autotopy_fixed_point D (g^[n]) (f^[n]) hq (autotopy_iterate D g f ha n) a hn

/-- The two cross identities compare an entire pair of rows. This gives a
smaller target for the remaining algebraic proof: equality of their indices
at just one point is enough. -/
theorem row_transport (c k g f : G → G) (hq : IsQuasigroup D)
    (ha : ∀ x y, D.op (g x) y = f (D.op x y))
    (hc : ∀ x y, D.op y (D.op (c x) (D.op x y)) = g x)
    (hk : ∀ x y, D.op y (D.op (k x) (D.op x y)) = x) (x y : G) :
    D.op (k (g x)) (f y) = D.op (c x) y := by
  obtain ⟨z, rfl⟩ := (hq.1 x).2 y
  apply (hq.1 z).1
  rw [← ha]
  exact (hk (g x) z).trans (hc x z).symm

/-- A single coincidence of the compared row indices settles the common maps.
The order-59 counterexample shows that the original candidate does not force
such a coincidence. The lemma remains useful for different compressions. -/
theorem trivial_of_row_coincidence (c k g f : G → G) (hq : IsQuasigroup D)
    (ha : ∀ x y, D.op (g x) y = f (D.op x y))
    (hc : ∀ x y, D.op y (D.op (c x) (D.op x y)) = g x)
    (hk : ∀ x y, D.op y (D.op (k x) (D.op x y)) = x)
    (a : G) (he : k (g a) = c a) : (∀ x, g x = x) ∧ (∀ x, f x = x) := by
  have hh := row_transport D c k g f hq ha hc hk a a
  rw [he] at hh
  exact output_fixed_point D g f hq ha a ((hq.1 (c a)).1 hh)

end Parastrophes.Eq917Image.SplitCandidate
