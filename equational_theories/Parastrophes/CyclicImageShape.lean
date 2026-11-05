import equational_theories.Parastrophes.Equation872ImageShape

/-!
# Cyclic tests constrain every possible division-image identity

Suppose the unary-right operation x*y=y-1 on Z/nZ satisfies a source law
exactly when n divides d, where d>0. Any single identity defining its finite
left-division image must have a variable on one side, the same rightmost
variable on the other, and rightmost depth exactly d. In addition, its
leftmost variable must be different: otherwise left projection would satisfy
the identity, although it cannot be a left-division operation.

These are necessary conditions on *every* proposed identity, with no bound on
its size or number of variables. They are not a characterization or a negative
answer to the single-equation question.
-/
namespace Parastrophes.CyclicImageShape
open Law FreeMagma Eq872ImageShape

def leftmost : FreeMagma Nat → Nat
  | .Leaf i => i
  | .Fork a _ => leftmost a

@[implicit_reducible] def leftProjection (G : Type) : Magma G := ⟨fun x _ => x⟩

private theorem eval_right {G : Type} (t : FreeMagma Nat) (v : Nat → G) :
    @evalInMagma _ G (rightProjection G) v t = v (rightmost t) := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => exact hb

private theorem eval_left {G : Type} (t : FreeMagma Nat) (v : Nat → G) :
    @evalInMagma _ G (leftProjection G) v t = v (leftmost t) := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb => exact ha

theorem rightmost_eq {L : NatMagmaLaw} {i : Nat} {t : FreeMagma Nat}
    (hp : @satisfies _ Bool (rightProjection Bool) L)
    (h : Characterizes .fin L .left ⟨.Leaf i,t⟩) : rightmost t = i := by
  have ht := (h Bool (rightProjection Bool) (inferInstance : Finite Bool)).mpr
    ⟨rightProjection Bool, hp, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  have he := ht (fun j => decide (j=i))
  change decide (i=i) = @evalInMagma _ Bool (rightProjection Bool) _ t at he
  rw [eval_right] at he
  exact of_decide_eq_true (he.symm.trans (by simp))

theorem leftmost_ne {L : NatMagmaLaw} {i : Nat} {t : FreeMagma Nat}
    (h : Characterizes .fin L .left ⟨.Leaf i,t⟩) : leftmost t ≠ i := by
  intro he
  have ht : @satisfies _ Bool (leftProjection Bool) (⟨.Leaf i,t⟩ : NatMagmaLaw) := by
    intro v
    change v i = @evalInMagma _ Bool (leftProjection Bool) v t
    rw [eval_left, he]
  have hq := characterizes_sideQuasigroup h Bool _ (inferInstance : Finite Bool) ht
  exact Bool.false_ne_true ((hq false).1 (a₁ := false) (a₂ := true) rfl)

theorem depth_eq {L : NatMagmaLaw} {d i : Nat} {t : FreeMagma Nat}
    (hd : 0 < d) (hp : @satisfies _ Bool (rightProjection Bool) L)
    (hs : ∀ n, @satisfies _ (ZMod n) (unshift n) L ↔ (d : ZMod n) = 0)
    (h : Characterizes .fin L .left ⟨.Leaf i,t⟩) : rightDepth t = d := by
  have hr := rightmost_eq hp h
  have hn : rightDepth t ≠ 0 := by
    intro hz
    cases t with
    | Leaf j => exact leftmost_ne h hr
    | Fork a b => simp [rightDepth] at hz
  have hd₁ : d ∣ rightDepth t := by
    letI : NeZero d := ⟨by omega⟩
    have ht := (h _ (shift d) (inferInstance : Finite (ZMod d))).mpr
      ⟨unshift d, (hs d).mpr (by simp), shift_division d⟩
    have he := ht (fun _ => 0)
    change (0 : ZMod d) = @evalInMagma _ _ (shift d) _ t at he
    rw [eval_shift, zero_add] at he
    exact (ZMod.natCast_eq_zero_iff _ _).mp he.symm
  have hd₂ : rightDepth t ∣ d := by
    let n := rightDepth t
    letI : NeZero n := ⟨hn⟩
    have ht : @satisfies _ (ZMod n) (shift n) (⟨.Leaf i,t⟩ : NatMagmaLaw) := by
      intro v
      change v i = @evalInMagma _ _ (shift n) v t
      rw [eval_shift, hr]
      change v i = v i + (n : ZMod n)
      simp
    obtain ⟨M, hM, hm⟩ := (h _ _ (inferInstance : Finite (ZMod n))).mp ht
    have he : M = unshift n :=
      division_unique (division_symm hm) (division_symm (shift_division n))
    rw [he] at hM
    exact (ZMod.natCast_eq_zero_iff d n).mp ((hs n).mp hM)
  exact Nat.dvd_antisymm hd₂ hd₁

theorem target_shape {L K : NatMagmaLaw} {d : Nat}
    (hd : 0 < d) (hp : @satisfies _ Bool (rightProjection Bool) L)
    (hs : ∀ n, @satisfies _ (ZMod n) (unshift n) L ↔ (d : ZMod n) = 0)
    (h : Characterizes .fin L .left K) :
    ∃ i t, (K = ⟨.Leaf i,t⟩ ∨ K = ⟨t,.Leaf i⟩) ∧
      rightmost t = i ∧ rightDepth t = d ∧ leftmost t ≠ i := by
  rcases K with ⟨a,b⟩
  cases a with
  | Leaf i => exact ⟨i,b,Or.inl rfl,rightmost_eq hp h,depth_eq hd hp hs h,leftmost_ne h⟩
  | Fork a₁ a₂ =>
    cases b with
    | Leaf i =>
      have ht : Characterizes .fin L .left ⟨.Leaf i,.Fork a₁ a₂⟩ := by
        intro G D hG
        constructor
        · intro hk; exact (h G D hG).mp (fun v => (hk v).symm)
        · intro hi v; exact ((h G D hG).mpr hi v).symm
      exact ⟨i,.Fork a₁ a₂,Or.inr rfl,rightmost_eq hp ht,depth_eq hd hp hs ht,leftmost_ne ht⟩
    | Fork b₁ b₂ =>
      let Z : Magma Bool := ⟨fun _ _ => false⟩
      have hz : @satisfies _ Bool Z (⟨.Fork a₁ a₂,.Fork b₁ b₂⟩ : NatMagmaLaw) := fun _ => rfl
      have hq := characterizes_sideQuasigroup h Bool Z (inferInstance : Finite Bool) hz
      exact (Bool.false_ne_true ((hq false).1 (a₁ := false) (a₂ := true) rfl)).elim

end Parastrophes.CyclicImageShape
