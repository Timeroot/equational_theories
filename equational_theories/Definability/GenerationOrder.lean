import equational_theories.Definability.Invariant
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-! Finite generation orders, and their preservation under term recovery.

These lemmas justify generation constraints in finite searches. They do not
assert that any particular search formula is unsatisfiable. -/

namespace Magma.GenerationOrder
variable {G : Type}

def Closed (f : G → G → G) (S : Set G) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, f a b ∈ S

def Generated (f : G → G → G) (seeds : Set G) (x : G) : Prop :=
  ∀ S : Set G, seeds ⊆ S → Closed f S → x ∈ S

def stage (f : G → G → G) (seeds : Set G) : Nat → Set G
  | 0 => seeds
  | k+1 => stage f seeds k ∪ {z | ∃ a ∈ stage f seeds k, ∃ b ∈ stage f seeds k, f a b = z}

theorem stage_step (f : G → G → G) (seeds : Set G) (k : Nat) :
    stage f seeds k ⊆ stage f seeds (k+1) := fun _ h => Or.inl h

theorem stage_mono (f : G → G → G) (seeds : Set G) : Monotone (stage f seeds) :=
  monotone_nat_of_le_succ (stage_step f seeds)

theorem generated_iff_stage (f : G → G → G) (seeds : Set G) (x : G) :
    Generated f seeds x ↔ ∃ k, x ∈ stage f seeds k := by
  constructor
  · intro h
    apply h {x | ∃ k, x ∈ stage f seeds k}
    · intro a ha
      exact ⟨0, ha⟩
    · intro a ha b hb
      obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj⟩ := hb
      exact ⟨max i j + 1, Or.inr ⟨a, stage_mono f seeds (le_max_left i j) hi,
        b, stage_mono f seeds (le_max_right i j) hj, rfl⟩⟩
  · rintro ⟨k, hk⟩ S hS hc
    have hall : ∀ k, stage f seeds k ⊆ S := by
      intro k
      induction k with
      | zero => exact hS
      | succ k ih =>
        intro z hz
        rcases hz with hz | ⟨a, ha, b, hb, rfl⟩
        · exact ih hz
        · exact hc a (ih ha) b (ih hb)
    exact hall k hk

noncomputable def depth (f : G → G → G) (seeds : Set G)
    (h : ∀ x, Generated f seeds x) (x : G) : Nat :=
  by classical exact Nat.find ((generated_iff_stage f seeds x).mp (h x))

theorem depth_mem (f : G → G → G) (seeds : Set G)
    (h : ∀ x, Generated f seeds x) (x : G) :
    x ∈ stage f seeds (depth f seeds h x) :=
  by classical exact Nat.find_spec ((generated_iff_stage f seeds x).mp (h x))

theorem depth_le (f : G → G → G) (seeds : Set G)
    (h : ∀ x, Generated f seeds x) (x : G) (k : Nat)
    (hx : x ∈ stage f seeds k) : depth f seeds h x ≤ k :=
  by classical exact Nat.find_min' ((generated_iff_stage f seeds x).mp (h x)) hx

theorem depth_zero_iff (f : G → G → G) (seeds : Set G)
    (h : ∀ x, Generated f seeds x) (x : G) :
    depth f seeds h x = 0 ↔ x ∈ seeds := by
  constructor
  · intro hx
    have hm := depth_mem f seeds h x
    simpa only [hx, stage] using hm
  · intro hx
    exact Nat.eq_zero_of_le_zero (depth_le f seeds h x 0 hx)

theorem smaller_parents (f : G → G → G) (seeds : Set G)
    (h : ∀ x, Generated f seeds x) (z : G) (hz : z ∉ seeds) :
    ∃ a b, f a b = z ∧ depth f seeds h a < depth f seeds h z ∧
      depth f seeds h b < depth f seeds h z := by
  have hm := depth_mem f seeds h z
  have hn : depth f seeds h z ≠ 0 := by
    exact fun hz0 => hz ((depth_zero_iff f seeds h z).mp hz0)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hk] at hm
  rcases hm with hm | ⟨a, ha, b, hb, he⟩
  · have hh := depth_le f seeds h z k hm
    omega
  · refine ⟨a, b, he, ?_, ?_⟩
    · have hh := depth_le f seeds h a k ha
      omega
    · have hh := depth_le f seeds h b k hb
      omega

/-- A strict total order whose initial segment contains the generators, and in
which each remaining point is a product of two earlier points. -/
structure Witness (f : G → G → G) (seeds : Set G) where
  before : G → G → Prop
  irrefl : ∀ x, ¬ before x x
  trans : ∀ x y z, before x y → before y z → before x z
  total : ∀ x y, x ≠ y → before x y ∨ before y x
  seeds_first : ∀ x ∈ seeds, ∀ y ∉ seeds, before x y
  parents : ∀ z ∉ seeds, ∃ a b, f a b = z ∧ before a z ∧ before b z

noncomputable def finiteWitness {n : Nat} (f : Fin n → Fin n → Fin n)
    (seeds : Set (Fin n)) (h : ∀ x, Generated f seeds x) : Witness f seeds := by
  classical
  let key (x : Fin n) := depth f seeds h x * n + x.val
  have key_lt : ∀ x y, depth f seeds h x < depth f seeds h y → key x < key y := by
    intro x y hxy
    have hm := Nat.mul_le_mul_right n hxy
    dsimp [key]
    nlinarith [x.isLt, y.isLt]
  have key_inj : Function.Injective key := by
    intro x y he
    have hd : depth f seeds h x = depth f seeds h y := by
      rcases lt_trichotomy (depth f seeds h x) (depth f seeds h y) with hh | hh | hh
      · have := key_lt x y hh
        omega
      · exact hh
      · have := key_lt y x hh
        omega
    apply Fin.ext
    dsimp [key] at he
    rw [hd] at he
    omega
  refine ⟨fun x y => key x < key y, fun x => Nat.lt_irrefl _,
    fun x y z hxy hyz => Nat.lt_trans hxy hyz, ?_, ?_, ?_⟩
  · intro x y hxy
    exact lt_or_gt_of_ne (fun he => hxy (key_inj he))
  · intro x hx y hy
    apply key_lt
    have hx0 := (depth_zero_iff f seeds h x).mpr hx
    have hy0 : depth f seeds h y ≠ 0 := fun hh => hy ((depth_zero_iff f seeds h y).mp hh)
    omega
  · intro z hz
    obtain ⟨a, b, he, ha, hb⟩ := smaller_parents f seeds h z hz
    exact ⟨a, b, he, key_lt a z ha, key_lt b z hb⟩

theorem Witness.generated [Finite G] {f : G → G → G} {seeds : Set G}
    (w : Witness f seeds) (z : G) : Generated f seeds z := by
  classical
  letI : IsTrans G w.before := ⟨w.trans⟩
  letI : Std.Irrefl w.before := ⟨w.irrefl⟩
  have hw := Finite.wellFounded_of_trans_of_irrefl w.before
  induction z using hw.induction with
  | h z ih =>
    intro S hs hc
    by_cases hz : z ∈ seeds
    · exact hs hz
    · obtain ⟨a, b, he, ha, hb⟩ := w.parents z hz
      rw [← he]
      exact hc a (ih a ha S hs hc) b (ih b hb S hs hc)

theorem closed_of_termDefinable {M N : Magma G} {S : Set G}
    (h : @Set.TermDefinable _ ∅ MagmaLanguage M.FOStructure _ N.FinArityOp)
    (hc : Closed M.op S) : Closed N.op S := by
  have hP : M.IsCloneInvariant (fun f => Closed f S) :=
    { fst := fun a ha b hb => ha
      snd := fun a ha b hb => hb
      comp := fun _ _ hf hg a ha b hb => hc _ (hf a ha b hb) _ (hg a ha b hb) }
  exact hP.of_termDefinable h

/-- Recovering the source operation by a term preserves all source generators. -/
theorem generated_of_recovery {M N : Magma G} {seeds : Set G} {x : G}
    (h : @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ M.FinArityOp)
    (hx : Generated M.op seeds x) : Generated N.op seeds x := by
  intro S hs hc
  exact hx S hs (closed_of_termDefinable h hc)

noncomputable def finiteWitness_of_recovery {n : Nat} {M N : Magma (Fin n)}
    (seeds : Set (Fin n))
    (h : @Set.TermDefinable _ ∅ MagmaLanguage N.FOStructure _ M.FinArityOp)
    (hg : ∀ x, Generated M.op seeds x) : Witness N.op seeds :=
  finiteWitness N.op seeds (fun x => generated_of_recovery h (hg x))

/-- info: 'Magma.GenerationOrder.finiteWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteWitness

/-- info: 'Magma.GenerationOrder.Witness.generated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.generated

/-- info: 'Magma.GenerationOrder.closed_of_termDefinable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closed_of_termDefinable

/-- info: 'Magma.GenerationOrder.generated_of_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms generated_of_recovery

/-- info: 'Magma.GenerationOrder.finiteWitness_of_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteWitness_of_recovery

end Magma.GenerationOrder
