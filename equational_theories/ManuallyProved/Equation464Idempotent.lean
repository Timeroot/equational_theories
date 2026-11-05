import equational_theories.ManuallyProved.Equation63Idempotent
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# An idempotent infinite E464 magma which is not a quasigroup

On the free group on countably many generators, put `x ◇ y = x * f(x⁻¹ * y)`.
E464 is exactly the unary condition `f(x⁻¹ * f(f(f(x)))) = x⁻¹`. We construct
such a total f with f(1)=1 and f(g₁)=f(g₂)=g₃, preserving a row collision.

The construction adapts the E63 completion, but the extra iterate requires
more than substituting two-step paths for edges. Write `Two E` for a two-step
path in a finite partial function E. In particular, the mixed invariant
`Two E h d → E h⁻¹ d → h=1` excludes a troublesome new chain before it can
arise. Collision invariants are tracked separately for E and Two E.

For an undefined input d, choose a fresh free generator c. Add d ↦ c and the
forced families h⁻¹*c ↦ h⁻¹ and c⁻¹*h*t ↦ c⁻¹*h, indexed respectively by
`Two E h d` and by `Two E h d` together with `Two E h⁻¹ t`. Projection to the
fresh generator separates most cases. The remaining cases are exactly those
controlled by the mixed and collision invariants. Crucially, new two-step
paths have only the three forms described in `Extension.NextTwo`.

Every preservation lemma below is proved before `Extension.next_ok` assembles
them. The existing greedy-chain theorem then meets every domain requirement,
giving a TOTAL function, not merely a finite successful experiment. This is
an ordinary Lean proof: no solver certificate, native check, or extra axiom.
-/

namespace Eq464Idempotent
open FreshGenerator
noncomputable section
abbrev G := FreeGroup Nat
abbrev Two (E : Rel G G) (x z : G) := ∃ y, E x y ∧ E y z

/-- Invariants sufficient for one fresh-generator extension. The inverse-side
paths in both collision conditions have length two. -/
structure OK (E : Rel G G) : Prop where
  finite : Set.Finite {(x,y) : G × G | E x y}
  func {x y z} : E x y → E x z → y=z
  base : E 1 1
  law {x y z w} : E x y → E y z → E z w → E (x⁻¹*w) x⁻¹
  one {x} : E x 1 → x=1
  inverse {x} : E x x⁻¹ → x=1
  inverseTwo {x} : Two E x x⁻¹ → x=1
  opposite {x y} : E x y → E x⁻¹ y → x=1
  mixed {x y} : Two E x y → E x⁻¹ y → x=1
  aux3 {x x' y z} : E x y → E x' y → Two E x⁻¹ z → x'=x*z → x'=x
  aux4 {x x' y z z'} : E x y → E x' y → Two E x⁻¹ z → Two E x'⁻¹ z' →
    x'*z'=x*z → x=x'
  aux3Two {x x' y z} : Two E x y → Two E x' y → Two E x⁻¹ z → x'=x*z → x'=x
  aux4Two {x x' y z z'} : Two E x y → Two E x' y → Two E x⁻¹ z → Two E x'⁻¹ z' →
    x'*z'=x*z → x=x'

namespace OK
variable {E : Rel G G} (h : OK E)
include h
theorem two_func {x y z} (hy : Two E x y) (hz : Two E x z) : y=z := by
  obtain ⟨a,ha,hb⟩ := hy
  obtain ⟨b,hc,hd⟩ := hz
  have he := h.func ha hc
  subst b
  exact h.func hb hd

theorem two_one {x} (hx : Two E x 1) : x=1 := by
  obtain ⟨y,ha,hb⟩ := hx
  exact h.one ((h.one hb) ▸ ha)

theorem from_one {y} (hy : E 1 y) : y=1 := h.func hy h.base

theorem two_from_one {y} (hy : Two E 1 y) : y=1 :=
  h.two_func hy ⟨1,h.base,h.base⟩

theorem two_finite : Set.Finite {(x,y) : G × G | Two E x y} := by
  apply Set.Finite.subset ((h.finite.prod h.finite).image
    (fun ((x,_),(_,z)) => (x,z)))
  rintro ⟨x,z⟩ ⟨y,ha,hb⟩
  exact ⟨((x,y),(y,z)), ⟨ha,hb⟩, rfl⟩
end OK

class Extension where
  E : Rel G G
  ok : OK E
  d : G
  not_def {y} : ¬E d y

namespace Extension
variable [Extension]
def old : Finset G := insert d <| ok.finite.toFinset.biUnion fun (a,b) => {a,b}
theorem mem_old {a b x} (h : E a b) (hx : x ∈ ({a,b} : Finset G)) : x ∈ old := by
  refine Finset.mem_insert_of_mem ?_
  simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Prod.exists]
  exact ⟨a,b,h,hx⟩
def c := FreeGroup.of (freshGeneratorName old)
def project (x : G) : ℤ := Multiplicative.toAdd <| FreshGenerator.projectFresh old x
@[simp] theorem project_one : project 1=0 := by simp [project]
@[simp] theorem project_mul (x y) : project (x*y)=project x+project y := by simp [project]
@[simp] theorem project_inv (x) : project x⁻¹ = -project x := by simp [project]
@[simp] theorem project_c : project c=1 := by
  simp [project,c,← FreshGenerator.freshGenerator.eq_1]
  rfl
@[simp] theorem project_d : project d=0 := FreshGenerator.projectFresh_old (by simp [old])
@[local aesop safe destruct]
theorem project_E {x y} (h : E x y) : project x=0 ∧ project y=0 := by
  constructor <;> (apply FreshGenerator.projectFresh_old; apply mem_old h; simp)
@[local aesop safe destruct]
theorem project_two {x y} (h : Two E x y) : project x=0 ∧ project y=0 := by
  obtain ⟨z,ha,hb⟩ := h
  exact ⟨(project_E ha).1,(project_E hb).2⟩

theorem d_ne_one : d ≠ 1 := fun h => not_def (h ▸ ok.base)
theorem no_two_one : ¬ Two E 1 d := fun h => d_ne_one (ok.two_from_one h)
theorem no_repeat {x} (h : E x d) (hp : Two E x d) : False := by
  obtain ⟨y,hy,hz⟩ := hp
  have he := ok.func hy h
  exact not_def (he ▸ hz)

theorem aux3' {x x' z} (hx : Two E x d) (hy : Two E x' d)
    (hz : Two E x⁻¹ z) : x' ≠ x*z := by
  intro he
  have hh := ok.aux3Two hx hy hz he
  have hzone : z=1 := by simpa [hh] using he.symm
  have hxone : x=1 := inv_eq_one.mp (ok.two_one (hzone ▸ hz))
  exact no_two_one (hxone ▸ hx)

/-- The four families in a single extension. -/
@[mk_iff] inductive Next : G → G → Prop
  | base {a b} : E a b → Next a b
  | new {a b} : a=d → b=c → Next a b
  | pos {h a b} : Two E h d → a=h⁻¹*c → b=h⁻¹ → Next a b
  | neg {h f a b} : Two E h d → Two E h⁻¹ f → a=c⁻¹*h*f → b=c⁻¹*h → Next a b

theorem next_func {x y z} : Next x y → Next x z → y=z
  | .base h, .base k => ok.func h k
  | .new _ h, .new _ k => h.trans k.symm
  | .pos h he hy, .pos k ke hz => by
    rw [ke, mul_right_cancel_iff, inv_inj] at he
    exact hy.trans (congrArg Inv.inv he.symm) |>.trans hz.symm
  | .neg h hp he rfl, .neg k kp ke rfl => by
    have hh : _ := he.symm.trans ke
    simp only [mul_assoc, mul_left_cancel_iff] at hh
    exact congrArg (fun x => c⁻¹*x) (ok.aux4Two h k hp kp hh.symm)
  | .base h, .new rfl _ | .new rfl _, .base h => (not_def h).elim
  | .base _, .pos _ he _ | .pos _ he _, .base _ |
    .base _, .neg _ _ he _ | .neg _ _ he _, .base _ |
    .new _ _, .pos _ he _ | .pos _ he _, .new _ _ |
    .new _ _, .neg _ _ he _ | .neg _ _ he _, .new _ _ |
    .pos _ _ _, .neg _ _ he _ | .neg _ _ he _, .pos _ _ _ => by
      apply_fun project at he
      aesop

/-- No two negative-family edges can be consecutive. -/
theorem neg_not_neg {h k f} (hh : Two E h d) (hk : Two E k d)
    (hf : Two E k⁻¹ f) : c⁻¹*h ≠ c⁻¹*k*f := by
  intro he
  have hke : h=k*f := by simpa only [mul_assoc,mul_left_cancel_iff] using he
  exact aux3' hk hh hf hke

/-- Classification of all two-step paths after extending. In particular, no
negative-family point starts a two-step path. -/
@[mk_iff] inductive NextTwo : G → G → Prop
  | base {x y} : Two E x y → NextTwo x y
  | new {h x y} : E h d → x=h → y=c → NextTwo x y
  | pos {h f x y} : Two E h d → E h⁻¹ f → x=h⁻¹*c → y=f → NextTwo x y

theorem next_two {x z} : Two Next x z → NextTwo x z := by
  rintro ⟨y,hy,hz⟩
  cases hy with
  | base ha =>
    cases hz with
    | base hb => exact .base ⟨y,ha,hb⟩
    | new he hf => exact .new (he ▸ ha) rfl hf
    | pos _ he _ | neg _ _ he _ => apply_fun project at he; aesop
  | new he hf =>
    subst x; subst y
    cases hz with
    | base h => have := project_E h; simp at this
    | new h _ => apply_fun project at h; simp at h
    | neg _ _ h _ => apply_fun project at h; aesop
    | pos h he _ =>
      have hh := congrArg (fun t => t*c⁻¹) he
      simp only [mul_assoc, mul_inv_cancel, mul_one] at hh
      exact (no_two_one (inv_eq_one.mp hh.symm ▸ h)).elim
  | pos h he hf =>
    subst x; subst y
    cases hz with
    | base hb => exact .pos h hb rfl rfl
    | new he _ =>
      have hh := ok.inverseTwo (he.symm ▸ h)
      exact (d_ne_one (by simpa [hh] using he.symm)).elim
    | pos _ he _ | neg _ _ he _ => apply_fun project at he; aesop
  | neg h hp he hf =>
    subst x; subst y
    cases hz with
    | base hb => have := project_E hb; aesop
    | new he _ | pos _ he _ => apply_fun project at he; aesop
    | neg k kp he _ => exact (neg_not_neg h k kp he).elim

theorem nextTwo_to_two {x z} : NextTwo x z → Two Next x z
  | .base ⟨y,ha,hb⟩ => ⟨y,.base ha,.base hb⟩
  | .new h rfl rfl => ⟨d,.base h,.new rfl rfl⟩
  | .pos h hf rfl rfl => ⟨_,.pos h rfl rfl,.base hf⟩


theorem next_shapes {x y} (h : Next x y) :
    E x y ∨ (x=d ∧ y=c) ∨ (project x=1 ∧ project y=0) ∨
      (project x= -1 ∧ project y= -1) := by
  cases h with
  | base h => exact Or.inl h
  | new hx hy => exact Or.inr (Or.inl ⟨hx,hy⟩)
  | pos h hx hy =>
    obtain ⟨hh,_⟩ := project_two h
    exact Or.inr (Or.inr (Or.inl (by simp [hx,hy,hh])))
  | neg h hf hx hy =>
    obtain ⟨hh,_⟩ := project_two h
    obtain ⟨_,hff⟩ := project_two hf
    exact Or.inr (Or.inr (Or.inr (by simp [hx,hy,hh,hff])))

theorem two_shapes {x y} (h : Two Next x y) :
    Two E x y ∨ (E x d ∧ y=c) ∨ (project x=1 ∧ project y=0) := by
  cases next_two h with
  | base h => exact Or.inl h
  | new h hx hy => exact Or.inr (Or.inl ⟨hx ▸ h,hy⟩)
  | pos h hf hx hy =>
    obtain ⟨hh,_⟩ := project_two h
    obtain ⟨_,hff⟩ := project_E hf
    exact Or.inr (Or.inr (by simp [hx,hy,hh,hff]))

theorem next_not_c {x} : ¬ Next c x := by
  intro h
  cases h with
  | base h => have hh := (project_E h).1; simp at hh
  | new he _ => have hh := congrArg project he; simp at hh
  | pos h he _ =>
    have hh := congrArg (fun t => t*c⁻¹) he
    simp only [mul_assoc,mul_inv_cancel,mul_one] at hh
    exact no_two_one (inv_eq_one.mp hh.symm ▸ h)
  | neg h hf he _ =>
    have hh := congrArg project he
    have hp := project_two h
    have hp' := project_two hf
    simp only [project_c,project_mul,project_inv] at hh
    omega

theorem next_law {x y z w} (h1 : Next x y) (h2 : Next y z) (h3 : Next z w) :
    Next (x⁻¹*w) x⁻¹ := by
  cases next_two ⟨y,h1,h2⟩ with
  | base h =>
    cases h3 with
    | base h3 =>
      obtain ⟨a,ha,hb⟩ := h
      exact .base (ok.law ha hb h3)
    | new hz hw => exact .pos (hz ▸ h) (by rw [hw]) rfl
    | pos _ he _ | neg _ _ he _ => apply_fun project at he; aesop
  | new h hx hz => exact (next_not_c (hz ▸ h3)).elim
  | pos h hf hx hz =>
    subst x; subst z
    cases h3 with
    | base h3 =>
      exact .neg h ⟨_,hf,h3⟩ (by group) (by group)
    | new he _ =>
      have hh := ok.mixed h (he ▸ hf)
      exact (no_two_one (hh ▸ h)).elim
    | pos _ he _ | neg _ _ he _ => apply_fun project at he; aesop

theorem next_one {x} (h : Next x 1) : x=1 := by
  rcases next_shapes h with h | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact ok.one h
  · have hh := congrArg project hy; simp at hh
  · cases h with
    | pos h he he' =>
      have ht : _ = (1:G) := he'.symm
      have ht' := inv_eq_one.mp ht
      exact (no_two_one (ht' ▸ h)).elim
    | base hb => have hh := (project_E hb).1; omega
    | new he _ => have hh := congrArg project he; simp only [project_d] at hh; omega
    | neg h hf he he' =>
      have hp := project_two h
      have hp' := project_two hf
      have hh := congrArg project he
      simp only [project_mul,project_inv,project_c] at hh
      omega
  · simp at hy

theorem next_inverse {x} (h : Next x x⁻¹) : x=1 := by
  rcases next_shapes h with h | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact ok.inverse h
  · have hh := congrArg project hx
    have ht := congrArg project hy
    simp only [project_d,project_c,project_inv] at *
    omega
  · simp only [project_inv] at hy; omega
  · simp only [project_inv] at hy; omega

theorem next_inverseTwo {x} (h : Two Next x x⁻¹) : x=1 := by
  rcases two_shapes h with h | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact ok.inverseTwo h
  · have hh := (project_E hx).1
    have ht := congrArg project hy
    simp only [project_c,project_inv] at ht
    omega
  · simp only [project_inv] at hy; omega

omit [Extension] in
theorem inverse_self {x : G} (h : x⁻¹=x) : x=1 := by
  apply pow_left_injective (n := 2) (by decide)
  calc x^2 = x*x⁻¹ := by rw [pow_two,h]
       _ = 1^2 := by simp

theorem next_old_or_new {x y} (h : Next x y) (hp : project x=0) :
    E x y ∨ (x=d ∧ y=c) := by
  rcases next_shapes h with h | h | ⟨hx,_⟩ | ⟨hx,_⟩
  · exact Or.inl h
  · exact Or.inr h
  · omega
  · omega

theorem next_opposite {x y} (h : Next x y) (h' : Next x⁻¹ y) : x=1 := by
  have hx : project x=0 := by
    rcases next_shapes h with h | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact (project_E h).1
    · simp [hx]
    · rcases next_shapes h' with h' | ⟨hx',hy'⟩ | ⟨hx',hy'⟩ | ⟨hx',hy'⟩
      · have hh := (project_E h').1; simp only [project_inv] at hh; omega
      · have hh := congrArg project hx'; simp only [project_inv,project_d] at hh; omega
      · simp only [project_inv] at hx'; omega
      · omega
    · rcases next_shapes h' with h' | ⟨hx',hy'⟩ | ⟨hx',hy'⟩ | ⟨hx',hy'⟩
      · have hh := (project_E h').1; simp only [project_inv] at hh; omega
      · have hh := congrArg project hx'; simp only [project_inv,project_d] at hh; omega
      · omega
      · simp only [project_inv] at hx'; omega
  rcases next_old_or_new h hx with h | ⟨hxd,hyc⟩
  · rcases next_old_or_new h' (by simp [hx]) with h' | ⟨_,hyc⟩
    · exact ok.opposite h h'
    · have hh := (project_E h).2; rw [hyc,project_c] at hh; omega
  · rcases next_old_or_new h' (by simp [hx]) with h' | ⟨hxd',_⟩
    · have hh := (project_E h').2; rw [hyc,project_c] at hh; omega
    · exact inverse_self (hxd'.trans hxd.symm)


theorem two_nonnegative {x y} (h : Two Next x y) : project x=0 ∨ project x=1 := by
  rcases two_shapes h with h | ⟨h,_⟩ | ⟨h,_⟩
  · exact Or.inl (project_two h).1
  · exact Or.inl (project_E h).1
  · exact Or.inr h

theorem prev_c {x} (h : Next x c) : x=d := by
  rcases next_shapes h with h | ⟨h,_⟩ | ⟨_,h⟩ | ⟨_,h⟩
  · have hh := (project_E h).2; simp at hh
  · exact h
  · simp at h
  · simp at h

theorem no_product {x y} (h : E x⁻¹ d) : ¬Next (x*c) y := by
  intro hn
  have hx : project x=0 := by have hh := (project_E h).1; simpa using hh
  cases hn with
  | base hb => have hh := (project_E hb).1; simp [hx] at hh
  | new he _ => have hh := congrArg project he; simp [hx] at hh
  | pos hp he _ =>
    have hh : _ := mul_right_cancel he
    have hh' := congrArg Inv.inv hh
    simp only [inv_inv] at hh'
    exact no_repeat h (hh'.symm ▸ hp)
  | neg hp hq he _ =>
    have hh := congrArg project he
    have ha := project_two hp
    have hb := project_two hq
    simp only [project_mul,project_inv,project_c,hx] at hh
    omega

theorem ep_cases {x y z} (h : Next x y) (hp : Two Next x⁻¹ z) :
    (E x y ∧ Two E x⁻¹ z) ∨
    (x=d ∧ y=c ∧ Two E x⁻¹ z) ∨
    (E x y ∧ E x⁻¹ d ∧ z=c) := by
  cases h with
  | base h =>
    cases next_two hp with
    | base hp => exact Or.inl ⟨h,hp⟩
    | new he hx hz => exact Or.inr (Or.inr ⟨h,hx ▸ he,hz⟩)
    | pos ha hb he _ =>
      have hh := congrArg project he
      have hx := project_E h
      have ht := project_two ha
      simp only [project_inv,project_mul,project_c] at hh
      omega
  | new hx hy =>
    subst x; subst y
    cases next_two hp with
    | base hp => exact Or.inr (Or.inl ⟨rfl,rfl,hp⟩)
    | new h he _ =>
      have hh : E d⁻¹ d := he ▸ h
      have hi := ok.inverse (x := d⁻¹) (by simpa using hh)
      exact (d_ne_one (inv_eq_one.mp hi)).elim
    | pos ha hb he _ =>
      have hh := congrArg project he
      have ht := project_two ha
      simp only [project_inv,project_mul,project_c,project_d] at hh
      omega
  | pos ha hx hy =>
    have hh := two_nonnegative hp
    have ht := project_two ha
    simp only [hx,project_inv,project_mul,project_c] at hh
    omega
  | neg ha hb hx hy =>
    subst x; subst y
    cases next_two hp with
    | base hp =>
      have hh := (project_two hp).1
      have hha := project_two ha
      have hhb := project_two hb
      simp only [project_inv,project_mul,project_c] at hh
      omega
    | new hp he _ =>
      have hh := (project_E (he ▸ hp)).1
      have hha := project_two ha
      have hhb := project_two hb
      simp only [project_inv,project_mul,project_c] at hh
      omega
    | pos hk hf he _ =>
      have hh := congrArg Inv.inv he
      simp only [inv_inv,mul_inv_rev,mul_assoc] at hh
      have hh' := mul_left_cancel hh
      exact (aux3' ha hk hb hh'.symm).elim

theorem next_mixed {x y} (h : Two Next x y) (h' : Next x⁻¹ y) : x=1 := by
  rcases ep_cases h' (by simpa only [inv_inv] using h) with
    ⟨he,hp⟩ | ⟨hx,hy,hp⟩ | ⟨he,hp,hy⟩
  · exact ok.mixed (by simpa only [inv_inv] using hp) he
  · have hh := (project_two hp).2; rw [hy,project_c] at hh; omega
  · have hh := (project_E he).2; rw [hy,project_c] at hh; omega

theorem next_aux3 {x x' y z} (h1 : Next x y) (h2 : Next x' y)
    (h3 : Two Next x⁻¹ z) (he : x'=x*z) : x'=x := by
  rcases ep_cases h1 h3 with ⟨h1,h3⟩ | ⟨hx,hy,h3⟩ | ⟨h1,h3,hz⟩
  · have hx := (project_E h1).1
    have hy := (project_E h1).2
    have hz := (project_two h3).2
    have hx' : project x'=0 := by simp [he,hx,hz]
    rcases next_old_or_new h2 hx' with h2 | ⟨_,hyy⟩
    · exact ok.aux3 h1 h2 h3 he
    · rw [hyy,project_c] at hy; omega
  · exact (prev_c (hy ▸ h2)).trans hx.symm
  · have hn := no_product (y := y) h3
    rw [hz] at he
    exact (hn (he ▸ h2)).elim

theorem finish_aux4 {x x' z z'} (hx : project x=0) (hx' : project x'=0)
    (old : Two E x⁻¹ z → Two E x'⁻¹ z' → x'*z'=x*z → x=x')
    (hz : Two E x⁻¹ z ∨ z=c) (hz' : Two E x'⁻¹ z' ∨ z'=c)
    (he : x'*z'=x*z) : x=x' := by
  rcases hz with hz | rfl <;> rcases hz' with hz' | rfl
  · exact old hz hz' he
  · have hh := congrArg project he
    have ht := (project_two hz).2
    simp only [project_mul,project_c,hx,hx'] at hh
    omega
  · have hh := congrArg project he
    have ht := (project_two hz').2
    simp only [project_mul,project_c,hx,hx'] at hh
    omega
  · exact (mul_right_cancel he).symm

theorem ep_weak {x y z} (h : Next x y) (hp : Two Next x⁻¹ z) :
    (E x y ∨ (x=d ∧ y=c)) ∧ (Two E x⁻¹ z ∨ z=c) := by
  rcases ep_cases h hp with ⟨h,hp⟩ | ⟨hx,hy,hp⟩ | ⟨h,_,hz⟩
  · exact ⟨Or.inl h,Or.inl hp⟩
  · exact ⟨Or.inr ⟨hx,hy⟩,Or.inl hp⟩
  · exact ⟨Or.inl h,Or.inr hz⟩

theorem next_aux4 {x x' y z z'} (h1 : Next x y) (h2 : Next x' y)
    (h3 : Two Next x⁻¹ z) (h4 : Two Next x'⁻¹ z') (he : x'*z'=x*z) : x=x' := by
  obtain ⟨hh1,hh3⟩ := ep_weak h1 h3
  obtain ⟨hh2,hh4⟩ := ep_weak h2 h4
  rcases hh1 with hh1 | ⟨hx,hy⟩
  · rcases hh2 with hh2 | ⟨hx',hy⟩
    · exact finish_aux4 (project_E hh1).1 (project_E hh2).1
        (fun ha hb he => ok.aux4 hh1 hh2 ha hb he) hh3 hh4 he
    · exact (prev_c (hy ▸ h1)).trans hx'.symm
  · exact hx.trans (prev_c (hy ▸ h2)).symm

theorem pp_weak {x y z} (h : Two Next x y) (hp : Two Next x⁻¹ z) :
    (Two E x y ∨ (E x d ∧ y=c)) ∧ (Two E x⁻¹ z ∨ z=c) := by
  have hx : project x=0 := by
    have hh := two_nonnegative h
    have ht := two_nonnegative hp
    simp only [project_inv] at ht
    omega
  constructor
  · rcases two_shapes h with hh | hh | ⟨hh,_⟩
    · exact Or.inl hh
    · exact Or.inr hh
    · omega
  · rcases two_shapes hp with hh | ⟨_,hh⟩ | ⟨hh,_⟩
    · exact Or.inl hh
    · exact Or.inr hh
    · simp only [project_inv] at hh; omega

theorem next_aux3Two {x x' y z} (h1 : Two Next x y) (h2 : Two Next x' y)
    (h3 : Two Next x⁻¹ z) (he : x'=x*z) : x'=x := by
  obtain ⟨hh1,hh3⟩ := pp_weak h1 h3
  rcases hh3 with hh3 | hz
  · have hz := (project_two hh3).2
    rcases hh1 with hh1 | ⟨hh1,hy⟩
    · have hx := (project_two hh1).1
      have hy := (project_two hh1).2
      rcases two_shapes h2 with hh2 | ⟨_,hy'⟩ | ⟨hx',_⟩
      · exact ok.aux3Two hh1 hh2 hh3 he
      · rw [hy',project_c] at hy; omega
      · simp [he,hx,hz] at hx'
    · have hx := (project_E hh1).1
      rcases two_shapes h2 with hh2 | ⟨hh2,_⟩ | ⟨hx',_⟩
      · have hh := (project_two hh2).2; rw [hy,project_c] at hh; omega
      · exact ok.aux3 hh1 hh2 hh3 he
      · simp [he,hx,hz] at hx'
  · have hh : E x⁻¹ d := by
      rcases two_shapes h3 with hh | ⟨hh,_⟩ | ⟨_,hh⟩
      · have ht := (project_two hh).2; rw [hz,project_c] at ht; omega
      · exact hh
      · rw [hz,project_c] at hh; omega
    obtain ⟨a,ha,_⟩ := h2
    rw [hz] at he
    exact (no_product hh (he ▸ ha)).elim

theorem next_aux4Two {x x' y z z'} (h1 : Two Next x y) (h2 : Two Next x' y)
    (h3 : Two Next x⁻¹ z) (h4 : Two Next x'⁻¹ z') (he : x'*z'=x*z) : x=x' := by
  obtain ⟨hh1,hh3⟩ := pp_weak h1 h3
  obtain ⟨hh2,hh4⟩ := pp_weak h2 h4
  rcases hh1 with hh1 | ⟨hh1,hy⟩ <;> rcases hh2 with hh2 | ⟨hh2,hy'⟩
  · exact finish_aux4 (project_two hh1).1 (project_two hh2).1
      (fun ha hb he => ok.aux4Two hh1 hh2 ha hb he) hh3 hh4 he
  · have hh := (project_two hh1).2; rw [hy',project_c] at hh; omega
  · have hh := (project_two hh2).2; rw [hy,project_c] at hh; omega
  · exact finish_aux4 (project_E hh1).1 (project_E hh2).1
      (fun ha hb he => ok.aux4 hh1 hh2 ha hb he) hh3 hh4 he


theorem next_finite : Set.Finite {(x,y) : G × G | Next x y} := by
  simp [next_iff,Set.setOf_or]
  split_ands
  · exact ok.finite
  · simp [← Prod.mk.injEq]
  · apply Set.Finite.subset (ok.two_finite.image (fun (x,_) => (x⁻¹*c,x⁻¹)))
    rintro ⟨a,b⟩ ⟨x,h,hx,hy⟩
    exact ⟨(x,d),h,Prod.ext hx.symm hy.symm⟩
  · apply Set.Finite.subset ((ok.two_finite.prod ok.two_finite).image
      (fun ((x,_),(_,y)) => (c⁻¹*x*y,c⁻¹*x)))
    rintro ⟨a,b⟩ ⟨x,h,y,hp,hx,hy⟩
    exact ⟨((x,d),(x⁻¹,y)),⟨h,hp⟩,Prod.ext hx.symm hy.symm⟩

theorem next_ok : OK Next where
  finite := next_finite
  func := next_func
  base := .base ok.base
  law := next_law
  one := next_one
  inverse := next_inverse
  inverseTwo := next_inverseTwo
  opposite := next_opposite
  mixed := next_mixed
  aux3 := next_aux3
  aux4 := next_aux4
  aux3Two := next_aux3Two
  aux4Two := next_aux4Two

end Extension

abbrev PartialSolution := {E : Rel G G // OK E}
def thomson (f : G → G) := ∀ x, f (x⁻¹*f (f (f x)))=x⁻¹

theorem exists_extension (seed : PartialSolution) :
    ∃ f : G → G, thomson f ∧ (∀ {x y}, seed.1 x y → f x=y) := by
  classical
  have ⟨c,hc,h1,h2,h3⟩ := exists_greedy_chain (a := seed)
    (task := fun x : G => {e | ∃ y, e.1 x y}) fun ⟨E,ok⟩ d => by
      if h : ∃ y, E d y then exact ⟨_,le_rfl,h⟩ else
      letI : Extension := { E,ok,d,not_def := fun h' => h ⟨_,h'⟩ }
      exact ⟨⟨Extension.Next,Extension.next_ok⟩,fun _ _ => (.base ·),_,.new rfl rfl⟩
  choose e he f hf using h3
  refine ⟨f,fun x => ?_,fun {x y} h => ?_⟩
  · let S : Finset G := {x,f x,f (f x),x⁻¹*f (f (f x))}
    have ⟨⟨e,he⟩,le⟩ := hc.directed.finset_le (hι := ⟨⟨_,h1⟩⟩)
      (S.image fun a => ⟨e a,he a⟩)
    replace le a ha := Finset.forall_mem_image.mp le ha a _ (hf a)
    simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq,S] at le
    obtain ⟨hx,hfx,hffx,ht⟩ := le
    exact e.2.func ht (e.2.law hx hfx hffx)
  · exact (e ..).2.func (h2 _ (he x) _ _ h) (hf ..) |>.symm

private abbrev g₁ := FreeGroup.of (1:Nat)
private abbrev g₂ := FreeGroup.of (2:Nat)
private abbrev g₃ := FreeGroup.of (3:Nat)
def seedList : List (G × G) := [(1,1),(g₁,g₃),(g₂,g₃)]
def seed : Rel G G := fun x y => (x,y) ∈ seedList

theorem seed_func {x y z} (h : seed x y) (h' : seed x z) : y=z := by
  have hc : ∀ a ∈ seedList, ∀ b ∈ seedList, a.1=b.1 → a.2=b.2 := by decide
  exact hc _ h _ h' rfl

theorem seed_two {x y} (h : Two seed x y) : x=1 ∧ y=1 := by
  obtain ⟨z,ha,hb⟩ := h
  have hc : ∀ a ∈ seedList, ∀ b ∈ seedList, a.2=b.1 → a.1=1 ∧ b.2=1 := by decide
  exact hc _ ha _ hb rfl

theorem seed_ok : OK seed where
  finite := List.finite_toSet seedList
  func := seed_func
  base := by simp [seed,seedList]
  law h1 h2 h3 := by
    obtain ⟨hx,hz⟩ := seed_two ⟨_,h1,h2⟩
    have hw := seed_func (hz ▸ h3) (show seed 1 1 by simp [seed,seedList])
    simp [hx,hw,seed,seedList]
  one h := by
    have hc : ∀ a ∈ seedList, a.2=1 → a.1=1 := by decide
    exact hc _ h rfl
  inverse h := by
    have hc : ∀ a ∈ seedList, a.2=a.1⁻¹ → a.1=1 := by decide
    exact hc _ h rfl
  inverseTwo h := (seed_two h).1
  opposite h h' := by
    have hc : ∀ a ∈ seedList, ∀ b ∈ seedList,
        b.1=a.1⁻¹ → a.2=b.2 → a.1=1 := by decide
    exact hc _ h _ h' rfl rfl
  mixed h _ := (seed_two h).1
  aux3 _ _ h he := by rw [(seed_two h).2,mul_one] at he; exact he
  aux4 _ _ h h' _ := (inv_eq_one.mp (seed_two h).1).trans
    (inv_eq_one.mp (seed_two h').1).symm
  aux3Two _ _ h he := by rw [(seed_two h).2,mul_one] at he; exact he
  aux4Two _ _ h h' _ := (inv_eq_one.mp (seed_two h).1).trans
    (inv_eq_one.mp (seed_two h').1).symm

/-- A total infinite E464 model with a collision in its identity row. -/
theorem countermodel : ∃ M : Magma (FreeGroup Nat),
    @Equation464 _ M ∧ (∀ x, M.op x x=x) ∧ ¬Function.Injective (M.op 1) := by
  obtain ⟨f,hf,he⟩ := exists_extension ⟨seed,seed_ok⟩
  refine ⟨⟨fun x y => x*f (x⁻¹*y)⟩,?_,?_,?_⟩
  · intro x y
    group
    have hh := congrArg (y*·) (hf (x⁻¹*y))
    group at hh
    exact hh.symm
  · intro x
    have ho : f 1=1 := he (by simp [seed,seedList])
    simp [ho]
  · intro hi
    have ha : f g₁=g₃ := he (by simp [seed,seedList])
    have hb : f g₂=g₃ := he (by simp [seed,seedList])
    have hh : g₁=g₂ := hi (by simpa using ha.trans hb.symm)
    exact (by decide : g₁≠g₂) hh

end
end Eq464Idempotent
