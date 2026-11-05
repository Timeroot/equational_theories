import equational_theories.Parastrophes.Equation917CancelComparison
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A central-shift obstruction for E917 image candidates

The carrier need not be an abelian group, and multiplication need not be
affine. Only a free additive action is assumed, with scalar effects a,b when
a shift is moved through the two inputs. Such actions occur on the fibres of
central extensions with arbitrary base multiplication and arbitrary offsets.

The main lemma below compares two evaluations of q(q(x)). It relates a
uniform unit displacement u to a uniform crossed displacement k. This is a
conditional structural calculation, not a catalogue characterization.
-/
namespace Parastrophes.Eq917Image.CentralShifts
open Law
open SandwichCandidate (U H F)

variable {A R : Type} [CommRing R]

structure Coordinates (D : Magma A) where
  shift : R → A → A
  a : R
  b : R
  zero : ∀ x, shift 0 x = x
  add : ∀ s t x, shift s (shift t x) = shift (s+t) x
  free : ∀ x, Function.Injective (fun s => shift s x)
  left : ∀ s x y, D.op (shift s x) y = shift (a*s) (D.op x y)
  right : ∀ s x y, D.op x (shift s y) = shift (b*s) (D.op x y)

variable (D : Magma A) (C : Coordinates (R := R) D)

theorem op_shift (s t : R) (x y : A) :
    D.op (C.shift s x) (C.shift t y) = C.shift (C.a*s+C.b*t) (D.op x y) := by
  rw [C.left, C.right, C.add]

theorem core_shift (s : R) (x : A) :
    core D (C.shift s x) =
      C.shift ((C.a^2+C.a^2*C.b+C.a*C.b^2+C.b)*s) (core D x) := by
  simp only [core, op_shift D C]
  congr 1
  ring

theorem H_first_shift (s : R) (x y : A) :
    H D (C.shift s x) y =
      C.shift ((C.a*(C.a^2+C.a^2*C.b+C.a*C.b^2+C.b)+C.b*C.a)*s) (H D x y) := by
  simp only [H, core_shift D C, C.left, C.right, C.add]
  congr 1
  ring

theorem H_second_shift (s : R) (x y : A) :
    H D x (C.shift s y) = C.shift (C.b^2*s) (H D x y) := by
  simp only [H, C.right]
  congr 1
  ring

/-- The crossed law with displacement k determines q(q(x)) up to a shift.
Comparing the diagonal crossed law with U(q(x)) then eliminates q entirely.
Both cancellations are explicit, so the lemma applies to non-affine bases. -/
theorem displacement_relation (hq : IsQuasigroup D) (ai bi u k : R)
    (ha : C.a*ai=1) (hb : C.b*bi=1)
    (hu : ∀ x, U D x = C.shift u x)
    (hf : ∀ x y, F D x y = C.shift k x) (o : A) :
    (C.a+C.b-C.b^2)*k = C.a*(1+C.b)*u := by
  let delta := ai*(bi-1)*k
  have had : C.a*delta+k=bi*k := by
    dsimp [delta]
    linear_combination (norm := ring_nf) (bi-1)*k*ha
  have hbk : C.b*(bi*k)=k := by rw [← mul_assoc, hb, one_mul]
  have qq (x : A) : core D (core D x) = C.shift delta (D.op x x) := by
    let p := D.op x (D.op x x)
    let z := D.op (core D x) p
    have first : D.op (core D (core D x)) z = C.shift (bi*k) x := by
      apply (hq.1 p).1
      have he := hf (core D x) p
      change D.op p (D.op (core D (core D x)) z) = C.shift k (D.op p x) at he
      rw [C.right, hbk]
      exact he
    have second : D.op (D.op x x) z = C.shift k x := hf x (D.op x x)
    apply (hq.2 z).1
    change D.op (core D (core D x)) z = D.op (C.shift delta (D.op x x)) z
    rw [first, C.left, second, C.add, had]
  have inner (x : A) :
      D.op (core D x) (D.op x x) = C.shift (u-C.b*delta) (core D x) := by
    have he := hu (core D x)
    change D.op (core D x) (core D (core D x)) = C.shift u (core D x) at he
    rw [qq, C.right] at he
    have hh := congrArg (C.shift (-(C.b*delta))) he
    rw [C.add, neg_add_cancel, C.zero, C.add] at hh
    simpa only [sub_eq_add_neg, add_comm] using hh
  have he := hf o o
  change D.op o (D.op (core D o) (D.op o o)) = C.shift k o at he
  rw [inner, C.right] at he
  change C.shift (C.b*(u-C.b*delta)) (U D o) = C.shift k o at he
  rw [hu, C.add] at he
  have hh := C.free o he
  dsimp [delta] at hh
  linear_combination (norm := ring_nf)
    -C.a*hh - C.b^2*k*(bi-1)*ha - C.b*k*hb

/-- The free outer parameter determines the relation a=-b³ whenever b is
invertible. This uses shifts of a parameter, not an affine formula for D. -/
theorem coefficient_relation (h : CancelComparison.Identity D) (bi : R)
    (hb : C.b*bi=1) (o : A) : C.a = -C.b^3 := by
  have he := h o o o o (C.shift 1 o)
  have hz := h o o o o o
  rw [C.right, C.right, H_second_shift D C, op_shift D C, ← hz] at he
  have hc := C.free o (he.symm.trans (C.zero o).symm)
  have heq : C.a*C.b+C.b^4=0 := by linear_combination (norm := ring_nf) hc
  linear_combination (norm := ring_nf) bi*heq - (C.a+C.b^3)*hb

theorem unit_coefficient (u : R) (hu : ∀ x, U D x = C.shift u x) (o : A) :
    C.a+C.b*(C.a^2+C.a^2*C.b+C.a*C.b^2+C.b)=1 := by
  have he := hu (C.shift 1 o)
  change D.op (C.shift 1 o) (core D (C.shift 1 o)) = C.shift u (C.shift 1 o) at he
  rw [core_shift D C, op_shift D C] at he
  change C.shift (C.a*1+C.b*((C.a^2+C.a^2*C.b+C.a*C.b^2+C.b)*1)) (U D o) = _ at he
  rw [hu, C.add, C.add] at he
  have hh := C.free o he
  linear_combination (norm := ring_nf) hh

theorem cross_coefficient (h : CancelComparison.Identity D) (o : A) :
    C.b*(C.a*(C.a^2+C.a^2*C.b+C.a*C.b^2+C.b)+C.b*C.a)=1 := by
  have he := h (C.shift 1 o) o o o o
  have hz := h o o o o o
  rw [H_first_shift D C, C.right, ← hz] at he
  have hh := C.free o he
  simpa only [mul_one] using hh.symm

/-- The 48-operation comparison is exact whenever its U-map is a uniform
central translation. The action is free, but need not be transitive: this
therefore covers non-affine base magmas as well as affine operations.

The key integral identity is unusually small: if
h=b⁶+b⁵+b³+1 and r=b³+b²+1, then h-b³r=1. No characteristic is excluded.
Uniformity of U is a hypothesis here, not a claimed general consequence. -/
theorem basis_of_uniform_shift (h : CancelComparison.Identity D)
    (hq : IsQuasigroup D) (bi u : R) (hb : C.b*bi=1)
    (hu : ∀ x, U D x = C.shift u x) (o : A) : Basis D := by
  have ha := coefficient_relation D C h bi hb o
  have hk := unit_coefficient D C u hu o
  have hx := cross_coefficient D C h o
  rw [ha] at hk hx
  have hp : C.b^6+C.b^5+C.b^3+1=0 := by
    linear_combination (norm := ring_nf) -hx - C.b^3*hk
  have weight : C.a^2-C.a-C.a*C.b^2 = -1 := by
    rw [ha]
    linear_combination (norm := ring_nf) hp
  have frame (x y : A) : D.op (C.shift (-u) y) (H D x y) = x := by
    obtain ⟨v, hv⟩ := (hq.1 (CancelComparison.rightTree D o o o)).2 y
    have he := h x o o o v
    have comparison : D.op (CancelComparison.leftTree D o o o) v =
        C.shift (-u) (D.op (CancelComparison.rightTree D o o o) v) := by
      simp only [CancelComparison.leftTree, CancelComparison.rightTree, hu,
        C.left, C.right, C.add]
      congr 1
      linear_combination (norm := ring_nf) u*weight
    rw [comparison, hv] at he
    exact he.symm
  have hf (x y : A) : F D x y = C.shift (C.a*u) x := by
    have he := frame x y
    rw [C.left] at he
    have hh := congrArg (C.shift (C.a*u)) he
    rw [C.add] at hh
    have hz : C.a*u+C.a*(-u)=0 := by ring
    rw [hz, C.zero] at hh
    exact hh
  have hai : C.a * (-(bi^3)) = 1 := by
    rw [ha, neg_mul_neg, ← mul_pow, hb, one_pow]
  have hd := displacement_relation D C hq (-(bi^3)) bi u (C.a*u) hai hb hu hf o
  have inj : Function.Injective (fun z : R => C.a*z) := by
    intro x y he
    have hh := congrArg (fun t => (-(bi^3))*t) he
    have hi : (-(bi^3))*C.a=1 := by rw [mul_comm]; exact hai
    simpa only [← mul_assoc, hi, one_mul] using hh
  have hr : (C.b^3+C.b^2+1)*u=0 := by
    have hh : (C.a+C.b-C.b^2)*u=(1+C.b)*u := by
      apply inj
      linear_combination (norm := ring_nf) hd
    rw [ha] at hh
    linear_combination (norm := ring_nf) -hh
  have uz : u=0 := by
    linear_combination (norm := ring_nf) u*hp - C.b^3*hr
  have unit (x : A) : U D x=x := by rw [hu, uz, C.zero]
  refine ⟨fun x => (unit x).symm, ?_⟩
  intro x y
  have he := frame x y
  rw [uz, neg_zero, C.zero] at he
  exact he.symm

/-- A single coincidence with a central shift makes the whole regular U-map
that same shift. The column through o reaches every point, determining d;
row cancellation then determines U. -/
theorem uniform_of_one_orbit (hq : IsQuasigroup D) (d : A → A)
    (hd : ∀ x y, D.op x (U D y) = d (D.op x y)) (o : A) (u : R)
    (ho : U D o = C.shift u o) : ∀ x, U D x = C.shift u x := by
  have dval (x : A) : d x = C.shift (C.b*u) x := by
    obtain ⟨y, rfl⟩ := (hq.2 o).2 x
    rw [← hd, ho, C.right]
  intro x
  apply (hq.1 o).1
  rw [hd, dval, C.right]

/-- Finite comparison models cannot be nontrivial central extensions of a
quotient with a U-fixed point. Only one point must have U in its shift orbit;
uniformity and invertibility of the scalar coefficient are derived. -/
theorem basis_of_one_orbit [Finite A] [Finite R]
    (h : CancelComparison.Identity D) (o : A) (u : R)
    (ho : U D o = C.shift u o) : Basis D := by
  letI : Nonempty A := ⟨o⟩
  have hq := CancelComparison.quasigroup D h
  obtain ⟨_, d, _, _, hd, _, _, _⟩ := CancelComparison.reduction D h
  have hu := uniform_of_one_orbit D C hq d hd o u ho
  have binj : Function.Injective (fun s : R => C.b*s) := by
    intro s t he
    change C.b*s=C.b*t at he
    apply C.free o
    apply (hq.1 o).1
    rw [C.right, C.right, he]
  obtain ⟨bi, hb⟩ := (Finite.surjective_of_injective binj) 1
  exact basis_of_uniform_shift D C h hq bi u hb hu o

section Extensions
variable {I : Type}

/-- Arbitrary base multiplication and arbitrary central offsets. The scalar
coefficients are not required to be invertible in the definition. -/
@[implicit_reducible] def extension (B : Magma I) (a b : R) (phi : I → I → R) :
    Magma (I × R) :=
  ⟨fun x y => (B.op x.1 y.1, a*x.2+b*y.2+phi x.1 y.1)⟩

def extensionCoordinates (B : Magma I) (a b : R) (phi : I → I → R) :
    Coordinates (R := R) (extension B a b phi) where
  shift s x := (x.1, s+x.2)
  a := a
  b := b
  zero x := by simp
  add s t x := by simp [add_assoc]
  free x := by
    intro s t he
    exact add_right_cancel (congrArg Prod.snd he)
  left s x y := by
    apply Prod.ext
    · rfl
    · change a*(s+x.2)+b*y.2+phi x.1 y.1 = a*s+(a*x.2+b*y.2+phi x.1 y.1)
      ring
  right s x y := by
    apply Prod.ext
    · rfl
    · change a*x.2+b*(s+y.2)+phi x.1 y.1 = b*s+(a*x.2+b*y.2+phi x.1 y.1)
      ring

/-- The candidate has its full converse on every finite central extension
of a genuine E917 image, with any offset table over any finite commutative
ring. This is a theorem about whole construction families, not a bounded
search. It does not assert that every finite magma is such an extension. -/
theorem extension_characterizes [Finite I] [Finite R]
    (B : Magma I) (a b : R) (phi : I → I → R) (hb : Basis B) :
    CancelComparison.Identity (extension B a b phi) ↔
      InImage Law917 .left (extension B a b phi) := by
  constructor
  · intro h
    apply (characterizes_fin _).mp
    cases isEmpty_or_nonempty I with
    | inl he =>
      letI := he
      exact ⟨fun x => isEmptyElim x.1, fun x => isEmptyElim x.1⟩
    | inr he =>
      letI := he
      let o : I := Classical.choice he
      let D := extension B a b phi
      let C := extensionCoordinates B a b phi
      let u := (U D (o, 0)).2
      apply basis_of_one_orbit D C h (o, 0) u
      apply Prod.ext
      · exact (hb.1 o).symm
      · change u = u+0
        exact (add_zero u).symm
  · exact CancelComparison.of_image _

theorem extension_candidate_base (B : Magma I) (a b : R) (phi : I → I → R)
    (h : CancelComparison.Identity (extension B a b phi)) :
    CancelComparison.Identity B := by
  intro x w y z v
  exact congrArg Prod.fst (h (x, 0) (w, 0) (y, 0) (z, 0) (v, 0))

/-- The converse is preserved when one adds a central-extension layer.
In particular it holds at every finite height over the one-element magma;
there is no bound on the offset tables or on the number of layers. -/
theorem extension_converse [Finite I] [Finite R]
    (B : Magma I) (a b : R) (phi : I → I → R)
    (hbase : CancelComparison.Identity B → Basis B)
    (h : CancelComparison.Identity (extension B a b phi)) :
    Basis (extension B a b phi) := by
  have hb := hbase (extension_candidate_base B a b phi h)
  exact (characterizes_fin _).mpr ((extension_characterizes B a b phi hb).mp h)

end Extensions

end Parastrophes.Eq917Image.CentralShifts
