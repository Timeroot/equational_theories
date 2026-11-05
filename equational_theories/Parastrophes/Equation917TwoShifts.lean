import equational_theories.Parastrophes.Equation917DoubleCandidate
import equational_theories.Parastrophes.Equation917FramePermutations

/-!
# A fifty-operation E917 candidate with two first-argument shifts

This is an OPEN candidate. No characterization attribute is registered.
Write q(x)=(x*(x*x))*x, U(x)=x*q(x), H(x,z)=q(x)*(x*z),
F(x,z)=z*H(x,z), G(w,z)=H(w*z,w), and

* A(x,z,w)=F(z,w)*H(x,z),
* B(x,z,w)=z*H(x,F(z,w)),
* C(x,z,w)=G(w,z)*H(x,z).

The proposed identity is `x=y*(K*(x*y))`, where
`K=(B(x,z,w)*(U(x)*A(x,v,t)))*C(x,r,s)`.
The eight variables are independent. A and B each have twelve operations,
C has sixteen, U has four, and the joining/frame operations add six.

Every true image satisfies the candidate. On finite carriers its independent
parameters force common permutations F(x,z)=a(x) and G(z,x)=b(x), together
with first-argument shifts a and b. The second shift is the extra information
compared with the earlier 46-operation candidate. The general converse is
still unproved: none of the reductions below asserts a=id or U=id.
-/
namespace Parastrophes.Eq917Image.TwoShifts
open DoubleCandidate (U B1 B2)
open SplitCandidate (F)
open SandwichCandidate (H G)

variable {A : Type} (D : Magma A)

def C (x z w : A) := D.op (G D w z) (H D x z)
def K (x z w v t r s : A) :=
  D.op (D.op (B2 D x z w) (D.op (U D x) (B1 D x v t))) (C D x r s)
def Identity : Prop := ∀ x y z w v t r s,
  x = D.op y (D.op (K D x z w v t r s) (D.op x y))

theorem of_basis (h : Basis D) (hq : IsSideQuasigroup .left D) : Identity D := by
  have hf (x z) : F D x z = x := (h.2 x z).symm
  have hg (w z) : G D w z = z := by
    apply (hq w).1
    exact hf (D.op w z) w
  have ha (x z w) : B1 D x z w = x := by
    simp only [B1, hf]
    exact (h.2 x z).symm
  have hb (x z w) : B2 D x z w = x := by
    simp only [B2, hf]
    exact (h.2 x z).symm
  have hc (x z w) : C D x z w = x := by
    simp only [C, hg]
    exact (h.2 x z).symm
  have hu (x) : U D x = x := (h.1 x).symm
  intro x y z w v t r s
  simp only [K, ha, hb, hc, hu]
  exact h.2 x y

theorem of_image (h : InImage Law917 .left D) : Identity D := by
  obtain ⟨M, hm, hd⟩ := h
  exact of_basis D (forward M D hd ((@Law917.models_iff A M).mp hm))
    (sideQuasigroup_of_division (division_symm hd))

theorem quasigroup [Finite A] (h : Identity D) : IsQuasigroup D :=
  Candidate.quasigroup_of_frame D (fun x z => K D x z x x x x x)
    (fun x y z => h x y z x x x x x)

theorem K_independent [Finite A] (h : Identity D)
    (x z w v t r s z' w' v' t' r' s' : A) :
    K D x z w v t r s = K D x z' w' v' t' r' s' := by
  have hq := quasigroup D h
  exact (hq.2 (D.op x x)).1 ((hq.1 x).1
    ((h x x z w v t r s).symm.trans (h x x z' w' v' t' r' s')))

theorem B1_independent [Finite A] (h : Identity D) (x v t v' t' : A) :
    B1 D x v t = B1 D x v' t' := by
  have hq := quasigroup D h
  have he := K_independent D h x x x v t x x x x v' t' x x
  exact (hq.1 (U D x)).1 ((hq.1 (B2 D x x x)).1 ((hq.2 (C D x x x)).1 he))

theorem C_independent [Finite A] (h : Identity D) (x r s r' s' : A) :
    C D x r s = C D x r' s' := by
  have he := K_independent D h x x x x x r s x x x x r' s'
  exact ((quasigroup D h).1 (D.op (B2 D x x x) (D.op (U D x) (B1 D x x x)))).1 he

theorem F_independent [Finite A] (h : Identity D) (x y z : A) :
    F D x y = F D x z := by
  exact ((quasigroup D h).2 (H D x x)).1 (B1_independent D h x x y x z)

theorem G_independent [Finite A] (h : Identity D) (x y z : A) :
    G D y x = G D z x := by
  exact ((quasigroup D h).2 (H D x x)).1 (C_independent D h x x y x z)

/-- Both first-argument shifts follow from independent parameters. The
result keeps all four bijectivity assertions explicit. -/
theorem common_maps [Finite A] (h : Identity D) :
    ∃ a b f g : A → A,
      Function.Bijective a ∧ Function.Bijective b ∧
      Function.Bijective f ∧ Function.Bijective g ∧
      (∀ x y, F D x y = a x) ∧ (∀ y x, G D y x = b x) ∧
      (∀ x y, D.op (a x) y = f (D.op x y)) ∧
      (∀ x y, D.op (b x) y = g (D.op x y)) ∧
      (∀ x y, D.op x (b y) = a (D.op x y)) := by
  let a := fun x => F D x x
  let b := fun x => G D x x
  let ac := fun x => B1 D x x x
  let bc := fun x => C D x x x
  have hf (x y) : F D x y = a x := F_independent D h x y x
  have hg (y x) : G D y x = b x := G_independent D h x y x
  have hq := quasigroup D h
  have hac (x y) : D.op (a y) (H D x y) = ac x :=
    B1_independent D h x y y x x
  obtain ⟨f, ha, hfb, _, hfa⟩ := SplitCandidate.common_permutations D
    (core D) a ac hq hf hac
  have mb (x y) : D.op x (b y) = a (D.op x y) := by
    rw [← hg x y]
    exact hf (D.op x y) x
  have hbi : Function.Injective b := by
    intro x y he
    apply (hq.1 x).1
    apply ha.1
    rw [← mb, ← mb, he]
  have hb : Function.Bijective b := ⟨hbi, Finite.surjective_of_injective hbi⟩
  let ae := Equiv.ofBijective a ha
  let g := fun x => bc (ae.symm x)
  have hbc (x y) : D.op (b y) (H D x y) = bc x :=
    C_independent D h x y y x x
  have hga (x y) : D.op (b x) y = g (D.op x y) := by
    let t := ae.symm (D.op x y)
    have ht : a t = D.op x y := ae.apply_symm_apply _
    have he : H D t x = y := (hq.1 x).1 ((hf t x).trans ht)
    calc
      _ = D.op (b x) (H D t x) := by rw [he]
      _ = bc t := hbc t x
      _ = _ := rfl
  have hgi : Function.Injective g := by
    intro x y he
    obtain ⟨u, hu⟩ := (hq.1 x).2 x
    obtain ⟨v, hv⟩ := (hq.1 x).2 y
    have hh : D.op (b x) u = D.op (b x) v := by rw [hga, hga, hu, hv]; exact he
    exact hu.symm.trans ((congrArg (D.op x) ((hq.1 (b x)).1 hh)).trans hv)
  exact ⟨a, b, f, g, ha, hb, hfb, ⟨hgi, Finite.surjective_of_injective hgi⟩,
    hf, hg, hfa, hga, mb⟩

/-- Values of the three independently parameterized subterms. In particular,
the second is f⁻¹(a(x)); using an inverse here requires f's proved bijectivity. -/
theorem bridge_values (a b f g : A → A)
    (hf : ∀ x y, F D x y = a x) (hg : ∀ y x, G D y x = b x)
    (hfa : ∀ x y, D.op (a x) y = f (D.op x y))
    (hga : ∀ x y, D.op (b x) y = g (D.op x y)) :
    (∀ x z w, B1 D x z w = f (a x)) ∧
    (∀ x z w, f (B2 D x z w) = a x) ∧
    (∀ x z w, C D x z w = g (a x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x z w
    simp only [B1, hf, hfa]
    exact congrArg f (hf x z)
  · intro x z w
    simp only [B2, hf]
    rw [← hfa]
    exact hf x (a z)
  · intro x z w
    simp only [C, hg, hga]
    exact congrArg g (hf x z)

/-- The exact term to use after the common-map reduction. The first factor
is f⁻¹(a(x)), not f(a(x)); keeping the inverse explicit avoids changing the
candidate when preparing an automated converse search. -/
theorem K_normalized (a b f g fi : A → A)
    (hf : ∀ x y, F D x y = a x) (hg : ∀ y x, G D y x = b x)
    (hfa : ∀ x y, D.op (a x) y = f (D.op x y))
    (hga : ∀ x y, D.op (b x) y = g (D.op x y))
    (hfi : Function.LeftInverse fi f) (x z w v t r s : A) :
    K D x z w v t r s =
      D.op (D.op (fi (a x)) (D.op (U D x) (f (a x)))) (g (a x)) := by
  have hv := bridge_values D a b f g hf hg hfa hga
  have hb : B2 D x z w = fi (a x) :=
    (hfi (B2 D x z w)).symm.trans (congrArg fi (hv.2.1 x z w))
  simp only [K, hb, hv.1, hv.2.2]

/-- Replace the outer two-variable frame by equality of entire rows. -/
theorem row_comparison [Finite A] (h : Identity D) (a b : A → A)
    (hf : ∀ x y, F D x y = a x)
    (mb : ∀ x y, D.op x (b y) = a (D.op x y)) (x z : A) :
    b (D.op (K D x x x x x x x) z) = D.op (core D x) z :=
  FramePermutations.row_comparison D.op (core D) a b
    (fun x => K D x x x x x x x) (quasigroup D h).1 hf mb
    (fun x y => (h x y x x x x x x).symm) x z

/-- Five commutation relations are proved. The sixth pair, b and g, is
deliberately not included: it is not an assumption available to a converse. -/
theorem commutations [Finite A] (h : Identity D) (a b f g : A → A)
    (hf : ∀ x y, F D x y = a x)
    (hfa : ∀ x y, D.op (a x) y = f (D.op x y))
    (hga : ∀ x y, D.op (b x) y = g (D.op x y))
    (mb : ∀ x y, D.op x (b y) = a (D.op x y)) :
    Function.Commute a f ∧ Function.Commute a g ∧ Function.Commute a b ∧
      Function.Commute f b ∧ Function.Commute f g := by
  let k := fun x => K D x x x x x x x
  have rows := (quasigroup D h).1
  have frame (x y) : D.op y (D.op (k x) (D.op x y)) = x :=
    (h x y x x x x x x).symm
  exact ⟨FramePermutations.commute_af D.op a b rows mb f hfa,
    FramePermutations.commute_ag D.op a b rows mb g hga,
    FramePermutations.commute_ab D.op (core D) a b k rows hf mb frame,
    FramePermutations.commute_fb D.op (core D) a b k rows hf mb frame f hfa,
    FramePermutations.commute_fg D.op (core D) a b k rows hf mb frame f g hfa hga⟩

/-- A single fixed point of the common F-map would finish the converse.
Thus a counterexample must have no such point anywhere, a stronger search
constraint than merely exhibiting one point that is moved. The existence
of a fixed point is still an additional, unproved hypothesis. -/
theorem basis_of_fixed_point [Finite A] (h : Identity D) (o : A)
    (ho : F D o o = o) : Basis D := by
  obtain ⟨a,b,f,g,_,_,_,_,hf,hg,hfa,hga,mb⟩ := common_maps D h
  have hq := quasigroup D h
  have hao : a o = o := (hf o o).symm.trans ho
  obtain ⟨ha,hf'⟩ := SplitCandidate.autotopy_fixed_point D a f hq hfa o hao
  have hb (x : A) : b x = x := by
    apply (hq.1 x).1
    rw [mb, ha]
  have hg' (x : A) : g x = x := by
    obtain ⟨y, rfl⟩ := (hq.1 o).2 x
    rw [← hga, hb]
  constructor
  · intro x
    have hk := K_normalized D a b f g id hf hg hfa hga
      (fun x => hf' x) x x x x x x x
    simp only [ha, hf', hg', id_eq] at hk
    have hr := row_comparison D h a b hf mb x x
    rw [hb] at hr
    have he := (hq.2 x).1 hr
    rw [hk] at he
    change D.op (D.op x (D.op (U D x) x)) x =
      D.op (D.op x (D.op x x)) x at he
    exact ((hq.2 x).1 ((hq.1 x).1 ((hq.2 x).1 he))).symm
  · intro x y
    exact ((hf x y).trans (ha x)).symm

end Parastrophes.Eq917Image.TwoShifts
