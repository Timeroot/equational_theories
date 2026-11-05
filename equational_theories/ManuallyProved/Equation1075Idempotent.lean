import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finset.Order
import Mathlib.Data.Rel
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Data.Finite.Prod
import equational_theories.FreshGenerator
import equational_theories.Equations.All

/-!
# A countable idempotent E1075 countermodel to left cancellation

On the countable free group, put `x ◇ y = x * f (x⁻¹ * y)`. The E1075
identity becomes `thomson f` below. Starting with `f 1 = 1` and
`f g₁ = f g₂ = g₃`, we complete a finite partial function while retaining
this collision. Idempotence follows from `f 1 = 1`.

For a missing argument `d`, choose a fresh group generator `c`. Besides
`f d = c`, only two kinds of forced values are needed:
* if `f (f h) = d⁻¹`, set `f (h⁻¹ * d⁻¹ * c) = h⁻¹`;
* if also `Q h q`, set `f (c⁻¹ * d * q) = c⁻¹ * d * h`.
Here `Q` records the partially defined expression
`q = h * f h⁻¹ * f ((f h⁻¹)⁻¹)`.

The auxiliary conditions in `OK` prevent these prescriptions from
conflicting, and are themselves preserved. The fresh generator has degree
1 under `project`, whereas every old value has degree 0. Thus the three
new input patterns have degrees 0, 1, and -1; most preservation cases
reduce to this separation. The remaining cases use group cancellation and
the auxiliary conditions. `sq_next`, `joint_next`, and `joint_sq_next`
classify the new partially defined expressions once, so the individual
invariant proofs can reuse them.

`exists_greedy_chain` schedules all group elements and takes the increasing
union. All preservation arguments and the small seed checks are verified
by Lean, without external proof certificates or native decision procedures.
-/

namespace Eq1075Free
private abbrev G := FreeGroup Nat
noncomputable section
open FreshGenerator

/-- The graph of the partially defined second iterate of the unary function. -/
def Sq (E : Rel G G) (x z : G) : Prop := ∃ y, E x y ∧ E y z
/-- A two-value expression used by the backward forced-value rule. -/
def Q (E : Rel G G) (x q : G) : Prop :=
  ∃ v w, E x⁻¹ v ∧ E v⁻¹ w ∧ q = x * v * w

/-- Finite partial functions admitting the fresh-generator extension.
These are construction invariants, not asserted consequences of E1075 in every model. -/
structure OK (E : Rel G G) : Prop where
  finite : Set.Finite {(x, y) : G × G | E x y}
  func {x y z} : E x y → E x z → y = z
  base : E 1 1
  law {x u v w} : E x u → E u v → E v⁻¹ w → E (x⁻¹ * v * w) x⁻¹
  zero {x} : E x 1 → x = 1
  anti {x} : E x x⁻¹ → x = 1
  period {x} : Sq E x x → x = 1
  twist {x y} : Sq E x y → E x⁻¹ y → x = 1
  qinj1 {x y t q} : E x t → E y t → Q E x q → Q E y q → x = y
  qinj2 {x y t q} : Sq E x t → Sq E y t → Q E x q → Q E y q → x = y
  qfiber1 {x t q} : E x t → Q E x q → E q t → x = 1
  qfiber2 {x t q} : Sq E x t → Q E x q → Sq E q t → x = 1
  qsquare {x t} : Sq E x t → Q E x t → x = 1

abbrev PartialSolution := {E : Rel G G // OK E}

class Extension where
  E : Rel G G
  ok : OK E
  d : G
  not_def {y} : ¬ E d y

namespace Extension
variable [Extension]

def old : Finset G := insert d <| ok.finite.toFinset.biUnion fun (a,b) => {a,b}
theorem mem_old {a b x} (h : E a b) (hx : x ∈ ({a,b} : Finset G)) : x ∈ old := by
  refine Finset.mem_insert_of_mem ?_
  simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Prod.exists]
  exact ⟨a,b,h,hx⟩
def c := FreshGenerator.freshGenerator old
def project (x : G) : ℤ := Multiplicative.toAdd <| FreshGenerator.projectFresh old x
@[simp] theorem project_one : project 1 = 0 := by simp [project]
@[simp] theorem project_mul {x y} : project (x*y) = project x + project y := by simp [project]
@[simp] theorem project_inv {x} : project x⁻¹ = -project x := by simp [project]
@[simp] theorem project_c : project c = 1 := by simp [project,c]; rfl
@[simp] theorem project_d : project d = 0 := FreshGenerator.projectFresh_old (by simp [old])
@[local aesop safe destruct]
theorem project_E {x y} (h : E x y) : project x = 0 ∧ project y = 0 := by
  constructor <;> (apply FreshGenerator.projectFresh_old; apply mem_old h; simp)
@[local aesop safe destruct]
theorem project_sq {x y} (h : Sq E x y) : project x = 0 ∧ project y = 0 := by
  obtain ⟨u,h1,h2⟩ := h
  exact ⟨(project_E h1).1,(project_E h2).2⟩
@[local aesop safe destruct]
theorem project_q {x y} (h : Q E x y) : project x = 0 ∧ project y = 0 := by
  obtain ⟨v,w,h1,h2,rfl⟩ := h
  have := project_E h1
  have := project_E h2
  simp_all

theorem d_ne_one : d ≠ 1 := by intro h; exact not_def (h ▸ ok.base)
theorem sq_one {x} (h : Sq E 1 x) : x = 1 := by
  obtain ⟨u,hu,hh⟩ := h
  have he := ok.func hu ok.base
  subst u
  exact ok.func hh ok.base

theorem no_q_link {x y q} (hx : Sq E x d⁻¹) (hy : Sq E y d⁻¹)
    (hq : Q E y q) (he : q = x) : False := by
  subst q
  have h := ok.qfiber2 hy hq hx
  subst y
  exact d_ne_one (inv_eq_one.mp (sq_one hy))
theorem no_q_square {x} (hx : Sq E x d⁻¹) (hq : Q E x d⁻¹) : False := by
  have h := ok.qsquare hx hq
  subst x
  exact d_ne_one (inv_eq_one.mp (sq_one hx))

@[mk_iff] inductive Next : G → G → Prop
  | base {a b} : E a b → Next a b
  | fresh {a b} : a = d → b = c → Next a b
  | forward {h a b} : Sq E h d⁻¹ → a = h⁻¹ * d⁻¹ * c → b = h⁻¹ → Next a b
  | backward {h q a b} : Sq E h d⁻¹ → Q E h q → a = c⁻¹ * d * q → b = c⁻¹ * d * h → Next a b

theorem next_d {y} : Next d y → y = c
  | .base h => (not_def h).elim
  | .fresh _ h => h
  | .forward _ he _ | .backward _ _ he _ => by
    apply_fun project at he
    aesop

theorem prev_c {x} : Next x c → x = d
  | .base h => by aesop
  | .fresh h _ => h
  | .forward _ _ he | .backward _ _ _ he => by
    apply_fun project at he
    aesop

theorem no_next_c {y} : ¬ Next c y := by
  intro h
  cases h with
  | base h => have := project_E h; simp_all
  | fresh he _ => have hh := congrArg project he; simp only [project_c, project_d] at hh; omega
  | forward hs he _ =>
    rename_i x hy
    have hg : x = d⁻¹ := by
      apply inv_injective
      have hh : 1 = x⁻¹ * d⁻¹ := mul_right_cancel (show 1*c = (x⁻¹*d⁻¹)*c from by simpa using he)
      simpa using eq_inv_of_mul_eq_one_left hh.symm
    subst_vars
    have hh := ok.period hs
    exact d_ne_one (inv_eq_one.mp hh)
  | backward hs hq he _ =>
    have hh := congrArg project he
    have hq0 := project_q hq
    simp only [project_c, project_d, project_inv, project_mul, hq0.2] at hh
    omega

theorem no_next_cinv {y} : ¬ Next c⁻¹ y := by
  intro h
  cases h with
  | base h => have := project_E h; simp_all
  | fresh he _ => have hh := congrArg project he; simp only [project_c, project_d, project_inv] at hh; omega
  | forward hs he _ =>
    have hh := congrArg project he
    have hh0 := project_sq hs
    simp only [project_c, project_d, project_inv, project_mul, hh0.1] at hh
    omega
  | backward hs hq he _ =>
    rename_i x q hy
    have hqv : q = d⁻¹ := by
      have hh : 1 = d * q := by
        apply mul_left_cancel (a := c⁻¹)
        simpa [mul_assoc] using he
      exact eq_inv_of_mul_eq_one_right hh.symm
    subst_vars
    exact no_q_square hs hq

theorem next_func {x y z} : Next x y → Next x z → y = z
  | .base h, .base h' => ok.func h h'
  | .fresh rfl rfl, .fresh rfl rfl => rfl
  | .forward h he hy, .forward h' he' hz => by
    rw [he', mul_left_inj, mul_left_inj, inv_inj] at he
    exact hz ▸ he ▸ hy
  | .backward h hq he rfl, .backward h' hq' rfl rfl => by
    simp only [mul_right_inj] at he
    rw [ok.qinj2 h h' hq (he ▸ hq')]
  | .base h, .fresh rfl rfl | .fresh rfl rfl, .base h => (not_def h).elim
  | .base .., .forward _ he _ | .forward _ he _, .base ..
  | .fresh .., .forward _ he _ | .forward _ he _, .fresh ..
  | .base .., .backward _ _ he _ | .backward _ _ he _, .base ..
  | .fresh .., .backward _ _ he _ | .backward _ _ he _, .fresh ..
  | .forward .., .backward _ _ he _ | .backward _ _ he _, .forward .. => by
    apply_fun project at he
    aesop

theorem next_zero_degree {x y} (hx : project x = 0) (h : Next x y) :
    E x y ∨ x = d ∧ y = c := by
  cases h with
  | base h => exact Or.inl h
  | fresh h h' => exact Or.inr ⟨h,h'⟩
  | forward _ he _ | backward _ _ he _ =>
    apply_fun project at he
    aesop

theorem next_old_degrees {x y} (hx : project x = 0) (hy : project y = 0)
    (h : Next x y) : E x y := by
  rcases next_zero_degree hx h with h | ⟨rfl,rfl⟩
  · exact h
  · simp at hy

/-- A new argument and its inverse cannot both be defined, except at `d` or `d⁻¹`. -/
theorem inv_in_E_means_d {x y z} :
    Next x y → Next x⁻¹ z → x = d ∨ x = d⁻¹ ∨ E x y ∧ E x⁻¹ z
  | .base _, .base _ | .fresh rfl rfl, _ => by tauto
  | _, .fresh h _ => by rw [inv_eq_iff_eq_inv] at h; tauto
  | .forward hs rfl rfl, .backward ht hq he _ => by
    have hh : _ = _ := he
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_right_inj] at hh
    exact (no_q_link hs ht hq hh.symm).elim
  | .backward hs hq rfl rfl, .forward ht he _ => by
    apply_fun Inv.inv at he
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_right_inj] at he
    exact (no_q_link ht hs hq he).elim
  | .base _, .forward _ he _ | .base _, .backward _ _ he _
  | .forward _ he _, .base _ | .backward _ _ he _, .base _
  | .forward .., .forward _ he _ | .backward .., .backward _ _ he _ => by
    apply_fun project at he
    aesop

/-- The only possible new two-step paths through the extended function. -/
theorem sq_next {x t} (h : Sq Next x t) :
    Sq E x t ∨ (E x d ∧ t = c) ∨
      ∃ a, Sq E a d⁻¹ ∧ E a⁻¹ t ∧ x = a⁻¹ * d⁻¹ * c := by
  obtain ⟨u,h1,h2⟩ := h
  cases h1 with
  | base h =>
    rcases next_zero_degree (project_E h).2 h2 with hh | ⟨rfl,rfl⟩
    · exact .inl ⟨_,h,hh⟩
    · exact .inr (.inl ⟨h,rfl⟩)
  | fresh hx hu => rw [hu] at h2; exact (no_next_c h2).elim
  | forward hs he hu =>
    subst u
    rcases next_zero_degree (by simp [(project_sq hs).1]) h2 with hh | ⟨hh,ht⟩
    · exact .inr (.inr ⟨_,hs,hh,he⟩)
    · have ha : _ = d⁻¹ := inv_eq_iff_eq_inv.mp hh
      rw [ha] at hs
      exact (d_ne_one (inv_eq_one.mp (ok.period hs))).elim
  | backward hs hq he hu =>
    subst u
    cases h2 with
    | backward ht hq' he' _ =>
      simp only [mul_right_inj] at he'
      exact (no_q_link hs ht hq' he'.symm).elim
    | base _ => aesop
    | fresh hh _ | forward _ hh _ =>
      apply_fun project at hh
      aesop

theorem fixed_old {x} (h : E x x) : x = 1 := ok.period ⟨x,h,h⟩

theorem q_fixed {x} (h : Q E x x) : x = 1 := by
  obtain ⟨v,w,hv,hw,he⟩ := h
  have hwv : w = v⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    apply mul_left_cancel (a := x)
    simpa [mul_assoc] using he.symm
  rw [hwv] at hw
  have hv1 : v = 1 := inv_eq_one.mp (fixed_old hw)
  rw [hv1] at hv
  exact inv_eq_one.mp (ok.zero hv)

/-- Simultaneously defined function values and `Q` expressions have three forms. -/
theorem joint_next {x u q} (hu : Next x u) (hq : Q Next x q) :
    (E x u ∧ Q E x q) ∨
    (E x u ∧ E x⁻¹ d⁻¹ ∧ q = x * d⁻¹ * c) ∨
    (x = d ∧ u = c ∧ Q E d q) := by
  obtain ⟨v,w,hv,hw,he⟩ := hq
  rcases inv_in_E_means_d hu hv with rfl | rfl | ⟨hu,hv⟩
  · have hu' := next_d hu
    rcases next_zero_degree (by simp) hv with hv | ⟨_,rfl⟩
    · rcases next_zero_degree (by simp [(project_E hv).2]) hw with hw | ⟨hv',rfl⟩
      · exact .inr (.inr ⟨rfl,hu',v,w,hv,hw,he⟩)
      · have hvd : v = d⁻¹ := inv_eq_iff_eq_inv.mp hv'
        rw [hvd] at hv
        exact (d_ne_one (inv_eq_one.mp (fixed_old hv))).elim
    · exact (no_next_cinv hw).elim
  · have hv' : v = c := next_d (by simpa using hv)
    subst v
    exact (no_next_cinv hw).elim
  · rcases next_zero_degree (by simp [(project_E hv).2]) hw with hw | ⟨hv',rfl⟩
    · exact .inl ⟨hu,v,w,hv,hw,he⟩
    · have hvd : v = d⁻¹ := inv_eq_iff_eq_inv.mp hv'
      subst v
      exact .inr (.inl ⟨hu,hv,he⟩)

/-- The corresponding four forms when a second iterate is also defined. -/
theorem joint_sq_next {x t q} (ht : Sq Next x t) (hq : Q Next x q) :
    (Sq E x t ∧ Q E x q) ∨
    (E x d ∧ Q E x q ∧ t = c) ∨
    (Sq E x t ∧ E x⁻¹ d⁻¹ ∧ q = x * d⁻¹ * c) ∨
    (E x d ∧ E x⁻¹ d⁻¹ ∧ t = c ∧ q = x * d⁻¹ * c) := by
  obtain ⟨u,hu,ht⟩ := ht
  rcases joint_next hu hq with ⟨hu,hq⟩ | ⟨hu,hv,hq⟩ | ⟨rfl,rfl,_⟩
  · rcases next_zero_degree (project_E hu).2 ht with ht | ⟨rfl,rfl⟩
    · exact .inl ⟨⟨u,hu,ht⟩,hq⟩
    · exact .inr (.inl ⟨hu,hq,rfl⟩)
  · rcases next_zero_degree (project_E hu).2 ht with ht | ⟨rfl,rfl⟩
    · exact .inr (.inr (.inl ⟨⟨u,hu,ht⟩,hv,hq⟩))
    · exact .inr (.inr (.inr ⟨hu,hv,rfl,hq⟩))
  · exact (no_next_c ht).elim

theorem next_law {x u v w} (hu : Next x u) (hv : Next u v) (hw : Next v⁻¹ w) :
    Next (x⁻¹ * v * w) x⁻¹ := by
  rcases sq_next ⟨u,hu,hv⟩ with h | ⟨h,rfl⟩ | ⟨a,ha,hv,rfl⟩
  · rcases next_zero_degree (by simp [(project_sq h).2]) hw with hw | ⟨he,rfl⟩
    · obtain ⟨u,hu,hv⟩ := h
      exact .base (ok.law hu hv hw)
    · have he' : v = d⁻¹ := inv_eq_iff_eq_inv.mp he
      subst v
      exact .forward h rfl rfl
  · exact (no_next_cinv hw).elim
  · rcases next_zero_degree (by simp [(project_E hv).2]) hw with hw | ⟨he,rfl⟩
    · apply Next.backward ha (show Q E a (a*v*w) from ⟨v,w,hv,hw,rfl⟩) <;> group
    · have he' : v = d⁻¹ := inv_eq_iff_eq_inv.mp he
      subst v
      have ha1 := ok.twist ha hv
      subst a
      exact (d_ne_one (inv_eq_one.mp (sq_one ha))).elim

theorem next_zero {x} : Next x 1 → x = 1
  | .base h => ok.zero h
  | .fresh _ he => by apply_fun project at he; simp at he
  | .forward hs _ he => by
    have hh := inv_eq_one.mp he.symm
    rw [hh] at hs
    exact (d_ne_one (inv_eq_one.mp (sq_one hs))).elim
  | .backward _ _ _ he => by apply_fun project at he; aesop

theorem next_anti {x} : Next x x⁻¹ → x = 1
  | .base h => ok.anti h
  | .fresh _ he | .forward _ he _ | .backward _ _ _ he => by
    apply_fun project at he
    aesop

theorem next_period {x} (h : Sq Next x x) : x = 1 := by
  rcases sq_next h with h | ⟨h,he⟩ | ⟨a,ha,h,he⟩
  · exact ok.period h
  · have hx := project_E h
    have hh := congrArg project he
    simp only [project_c] at hh
    omega
  · have hx := project_E h
    have ha0 := project_sq ha
    have hh := congrArg project he
    simp only [project_mul, project_inv, project_d, project_c] at hh
    omega

theorem next_twist {x y} (hs : Sq Next x y) (h : Next x⁻¹ y) : x = 1 := by
  rcases sq_next hs with hs0 | ⟨hxd,rfl⟩ | ⟨a,ha,hy,rfl⟩
  · exact ok.twist hs0 (next_old_degrees (by simp [(project_sq hs0).1]) (project_sq hs0).2 h)
  · have hx : x = d⁻¹ := inv_eq_iff_eq_inv.mp (prev_c h)
    subst x
    have hd : d⁻¹ = 1 := ok.anti (by simpa using hxd)
    exact hd
  · cases h with
    | base h => aesop
    | fresh he _ | forward _ he _ | backward _ _ _ he =>
      apply_fun project at he
      aesop

theorem next_qinj1 {x y t q} (hx : Next x t) (hy : Next y t)
    (hqx : Q Next x q) (hqy : Q Next y q) : x = y := by
  rcases joint_next hx hqx with ⟨hx0,hqx0⟩ | ⟨hx0,hxi,rfl⟩ | ⟨rfl,rfl,hqd⟩
  · rcases joint_next hy hqy with ⟨hy0,hqy0⟩ | ⟨hy0,hyi,he⟩ | ⟨rfl,rfl,_⟩
    · exact ok.qinj1 hx0 hy0 hqx0 hqy0
    · have hq0 := project_q hqx0
      have hy0' := project_E hy0
      have hh := congrArg project he
      simp only [project_mul,project_inv,project_c,project_d] at hh
      omega
    · have hh := project_E hx0; simp at hh
  · rcases joint_next hy hqy with ⟨hy0,hqy0⟩ | ⟨hy0,hyi,he⟩ | ⟨rfl,rfl,_⟩
    · have hq0 := project_q hqy0
      have hx0' := project_E hx0
      simp only [project_mul,project_inv,project_c,project_d] at hq0
      omega
    · simpa only [mul_left_inj] using he
    · have hh := project_E hx0; simp at hh
  · rcases joint_next hy hqy with ⟨hy0,_⟩ | ⟨hy0,_,_⟩ | ⟨rfl,_,_⟩
    · have hh := project_E hy0; simp at hh
    · have hh := project_E hy0; simp at hh
    · rfl

theorem next_qinj2 {x y t q} (hx : Sq Next x t) (hy : Sq Next y t)
    (hqx : Q Next x q) (hqy : Q Next y q) : x = y := by
  rcases joint_sq_next hx hqx with ⟨hx0,hqx0⟩ | ⟨hx0,hqx0,ht⟩ |
    ⟨hx0,hxi,hq⟩ | ⟨hx0,hxi,ht,hq⟩ <;>
  rcases joint_sq_next hy hqy with ⟨hy0,hqy0⟩ | ⟨hy0,hqy0,ht'⟩ |
    ⟨hy0,hyi,hq'⟩ | ⟨hy0,hyi,ht',hq'⟩
  all_goals first
    | exact ok.qinj2 hx0 hy0 hqx0 hqy0
    | exact ok.qinj1 hx0 hy0 hqx0 hqy0
    | exact mul_right_cancel (mul_right_cancel (hq.symm.trans hq'))
    | aesop

theorem next_qfiber1 {x t q} (hx : Next x t) (hq : Q Next x q)
    (ht : Next q t) : x = 1 := by
  rcases joint_next hx hq with ⟨hx0,hq0⟩ | ⟨hx0,hxi,rfl⟩ | ⟨rfl,rfl,hqd⟩
  · exact ok.qfiber1 hx0 hq0 (next_old_degrees (project_q hq0).2 (project_E hx0).2 ht)
  · cases ht with
    | forward ha he hy =>
      have hxa := mul_right_cancel (mul_right_cancel he)
      apply fixed_old
      simpa only [hy.trans hxa.symm] using hx0
    | base _ => aesop
    | fresh he _ =>
      have hh := congrArg project he
      have hx0' := project_E hx0
      simp only [project_mul,project_inv,project_c,project_d] at hh
      omega
    | backward hs hq he _ =>
      have hh := congrArg project he
      have hx0' := project_E hx0
      have hq0 := project_q hq
      simp only [project_mul,project_inv,project_c,project_d] at hh
      omega
  · have hqd' := prev_c ht
    subst q
    exact q_fixed hqd

theorem no_sq_direct {a} (hs : Sq E a d⁻¹) (he : E a d⁻¹) : False := by
  obtain ⟨b,hab,hbs⟩ := hs
  have hb := ok.func hab he
  rw [hb] at hbs
  exact d_ne_one (inv_eq_one.mp (fixed_old hbs))

theorem no_sq_fresh_q {x t} (hx : project x = 0) (hxi : E x⁻¹ d⁻¹) :
    ¬ Sq Next (x * d⁻¹ * c) t := by
  intro hs
  rcases sq_next hs with hs0 | ⟨he,_⟩ | ⟨a,ha,_,he⟩
  · have hh := (project_sq hs0).1
    simp [hx] at hh
  · have hh := (project_E he).1
    simp [hx] at hh
  · have hxa : x = a⁻¹ := mul_right_cancel (mul_right_cancel he)
    exact no_sq_direct ha (by simpa [hxa] using hxi)

theorem next_qfiber2 {x t q} (hx : Sq Next x t) (hq : Q Next x q)
    (ht : Sq Next q t) : x = 1 := by
  rcases joint_sq_next hx hq with ⟨hx0,hq0⟩ | ⟨hx0,hq0,rfl⟩ |
    ⟨hx0,hxi,rfl⟩ | ⟨hx0,hxi,rfl,rfl⟩
  · rcases sq_next ht with ht0 | ⟨ht0,he⟩ | ⟨a,ha,ht0,he⟩
    · exact ok.qfiber2 hx0 hq0 ht0
    · have hh := congrArg project he
      have hh0 := (project_sq hx0).2
      simp only [project_c] at hh
      omega
    · have hh := congrArg project he
      have hh0 := (project_q hq0).2
      have ha0 := (project_sq ha).1
      simp only [project_mul,project_inv,project_c,project_d] at hh
      omega
  · rcases sq_next ht with ht0 | ⟨ht0,_⟩ | ⟨a,ha,ht0,he⟩
    · have hh := (project_sq ht0).2; simp at hh
    · exact ok.qfiber1 hx0 hq0 ht0
    · have hh := (project_E ht0).2; simp at hh
  · exact (no_sq_fresh_q (project_sq hx0).1 hxi ht).elim
  · exact (no_sq_fresh_q (project_E hx0).1 hxi ht).elim

theorem next_qsquare {x t} (hx : Sq Next x t) (hq : Q Next x t) : x = 1 := by
  rcases joint_sq_next hx hq with ⟨hx0,hq0⟩ | ⟨hx0,hq0,rfl⟩ |
    ⟨hx0,hxi,he⟩ | ⟨hx0,hxi,rfl,he⟩
  · exact ok.qsquare hx0 hq0
  · have hh := (project_q hq0).2; simp at hh
  · have hh := congrArg project he
    have hx0' := project_sq hx0
    simp only [project_mul,project_inv,project_c,project_d] at hh
    omega
  · have hxd : x = d := by
      have hh : 1 = x * d⁻¹ := mul_right_cancel (show 1*c = (x*d⁻¹)*c from by simpa using he)
      simpa using eq_inv_of_mul_eq_one_left hh.symm
    exact (not_def (hxd ▸ hx0)).elim

theorem sq_finite : Set.Finite {(x,y) : G × G | Sq E x y} := by
  apply Set.Finite.subset ((ok.finite.prod ok.finite).image fun ((x,_),(_,y)) => (x,y))
  intro (x,y) ⟨u,hx,hy⟩
  exact ⟨((x,u),(u,y)),⟨hx,hy⟩,rfl⟩

theorem q_finite : Set.Finite {(x,y) : G × G | Q E x y} := by
  apply Set.Finite.subset ((ok.finite.prod ok.finite).image fun ((a,v),(_,w)) => (a⁻¹,a⁻¹*v*w))
  intro (x,y) h
  obtain ⟨v,w,hv,hw,he⟩ := h
  exact ⟨((x⁻¹,v),(v⁻¹,w)),⟨hv,hw⟩,by simp [he]⟩

theorem next_finite : Set.Finite {(x,y) : G × G | Next x y} := by
  simp [next_iff, Set.setOf_or]
  split_ands
  · exact ok.finite
  · simp [← Prod.mk.injEq]
  · apply Set.Finite.subset (sq_finite.image fun (x,_) => (x⁻¹*d⁻¹*c,x⁻¹))
    intro (a,b) ⟨x,hx,ha,hb⟩
    exact ⟨(x,d⁻¹),hx,Prod.ext ha.symm hb.symm⟩
  · apply Set.Finite.subset ((sq_finite.prod q_finite).image
      fun ((x,_),(_,q)) => (c⁻¹*d*q,c⁻¹*d*x))
    intro (a,b) ⟨x,hx,q,hq,ha,hb⟩
    exact ⟨((x,d⁻¹),(x,q)),⟨hx,hq⟩,Prod.ext ha.symm hb.symm⟩

def next : PartialSolution := ⟨Next, {
  finite := next_finite
  func := next_func
  base := .base ok.base
  law := next_law
  zero := next_zero
  anti := next_anti
  period := next_period
  twist := next_twist
  qinj1 := next_qinj1
  qinj2 := next_qinj2
  qfiber1 := next_qfiber1
  qfiber2 := next_qfiber2
  qsquare := next_qsquare }⟩

end Extension

/-- The unary functional equation that makes `x * f (x⁻¹ * y)` satisfy E1075. -/
def thomson (f : G → G) : Prop :=
  ∀ x, f (x⁻¹ * f (f x) * f ((f (f x))⁻¹)) = x⁻¹

/-- Complete any seed satisfying the invariants without changing its prescribed values. -/
theorem exists_extension (seed : PartialSolution) :
    ∃ f : G → G, thomson f ∧ (∀ {x y}, seed.1 x y → f x = y) := by
  classical
  have ⟨chain, hc, h1, h2, h3⟩ := exists_greedy_chain (a := seed)
    (task := fun x : _ => {e | ∃ y, e.1 x y}) fun ⟨E, ok⟩ d => by
      if h : ∃ y, E d y then exact ⟨_,le_rfl,h⟩ else
      let E1 : Extension := { E, ok, d, not_def := fun h' => h ⟨_,h'⟩ }
      exact ⟨E1.next,fun _ _ => (.base ·),_,.fresh rfl rfl⟩
  choose e he f hf using h3
  refine ⟨f,fun x => ?_,fun {x y} h => ?_⟩
  · let S : Finset G := {x, f x, (f (f x))⁻¹, x⁻¹ * f (f x) * f ((f (f x))⁻¹)}
    have ⟨⟨e,he⟩,le⟩ := hc.directed.finset_le (hι := ⟨⟨_,h1⟩⟩)
      (S.image fun a => ⟨e a,he a⟩)
    replace le a ha := Finset.forall_mem_image.mp le ha a _ (hf a)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨fx,ffx,finv,ffinal⟩ := le
    exact e.2.func ffinal (e.2.law fx ffx finv)
  · exact (e ..).2.func (h2 _ (he x) _ _ h) (hf ..) |>.symm

private abbrev g₁ : G := FreeGroup.of 1
private abbrev g₂ : G := FreeGroup.of 2
private abbrev g₃ : G := FreeGroup.of 3

def seedList : List (G × G) := [(1,1),(g₁,g₃),(g₂,g₃)]
def seed : Rel G G := fun x y => (x,y) ∈ seedList

theorem sq_seed {x y} (h : Sq seed x y) : x = 1 ∧ y = 1 := by
  obtain ⟨u,hx,hy⟩ := h
  have hh : ∀ a ∈ seedList, ∀ b ∈ seedList, b.1 = a.2 → a.1 = 1 ∧ b.2 = 1 := by decide
  exact hh _ hx _ hy rfl

theorem q_seed {x q} (h : Q seed x q) : x = 1 ∧ q = 1 := by
  obtain ⟨v,w,hv,hw,he⟩ := h
  have hh : ∀ a ∈ seedList, ∀ b ∈ seedList,
      b.1 = a.2⁻¹ → a.1 = 1 ∧ a.2 = 1 ∧ b.2 = 1 := by decide
  have ⟨hx,hv1,hw1⟩ := hh _ hv _ hw rfl
  change v = 1 at hv1
  change w = 1 at hw1
  have hx1 := inv_eq_one.mp hx
  exact ⟨hx1,by simp [he,hx1,hv1,hw1]⟩

theorem seed_ok : OK seed where
  finite := List.finite_toSet seedList
  func h1 h2 := by
    suffices ∀ a ∈ seedList, ∀ b ∈ seedList, a.1 = b.1 → a.2 = b.2 from this _ h1 _ h2 rfl
    decide
  base := by simp [seed,seedList]
  law h1 h2 h3 := by
    obtain ⟨rfl,rfl⟩ := sq_seed ⟨_,h1,h2⟩
    have hh : ∀ a ∈ seedList, a.1 = 1 → a.2 = 1 := by decide
    have hw := hh _ h3 (by simp)
    dsimp only at hw
    simp [hw,seed,seedList]
  zero h := by
    suffices ∀ a ∈ seedList, a.2 = 1 → a.1 = 1 from this _ h rfl
    decide
  anti h := by
    suffices ∀ a ∈ seedList, a.2 = a.1⁻¹ → a.1 = 1 from this _ h rfl
    decide
  period h := (sq_seed h).1
  twist h _ := (sq_seed h).1
  qinj1 _ _ h1 h2 := (q_seed h1).1.trans (q_seed h2).1.symm
  qinj2 _ _ h1 h2 := (q_seed h1).1.trans (q_seed h2).1.symm
  qfiber1 _ h _ := (q_seed h).1
  qfiber2 _ h _ := (q_seed h).1
  qsquare h _ := (sq_seed h).1

/-- An idempotent, countable E1075 model with a noninjective left translation. -/
theorem countermodel : ∃ (M : Magma (FreeGroup Nat)),
    @Equation1075 _ M ∧ (∀ x, M.op x x = x) ∧ ¬ Function.Injective (M.op 1) := by
  obtain ⟨f,h1075,hf⟩ := exists_extension ⟨seed,seed_ok⟩
  refine ⟨{op := fun x y => x * f (x⁻¹ * y)}, ?_, ?_, ?_⟩
  · intro x y
    group
    have hh := congr_arg (y * ·) (h1075 (x⁻¹ * y))
    group at hh
    exact hh.symm
  · intro x
    have h1 : f 1 = 1 := hf (by simp [seed,seedList])
    simp [h1]
  · intro hi
    have h1 : f g₁ = g₃ := hf (by simp [seed,seedList])
    have h2 : f g₂ = g₃ := hf (by simp [seed,seedList])
    have he : g₁ = g₂ := hi (by simpa using h1.trans h2.symm)
    exact (by decide : g₁ ≠ g₂) he

end
end Eq1075Free
