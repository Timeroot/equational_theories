import equational_theories.Definability.EventualRowCounting

/-!
# An upper bound for E3253 operation tables

The orbit of a row's diagonal point is fixed, a two-cycle through that point,
a distinct fixed point, or a two-cycle reached in one step. The four orbit
shapes each contribute at most n^(n-1) rows. Thus there are at most
4^n (n^(n-1))^n labeled E3253 tables.
-/

open Law Law.MagmaLaw
namespace EventualRowUpperCounting
variable {A : Type} [Fintype A] [DecidableEq A]

abbrev Triple (a b c : A) := {f : A → A // f a = b ∧ f b = c ∧ f c = b}
abbrev Third (a b : A) := {c : A // c ∉ ({a,b} : Finset A)}
abbrev Long (a : A) := Σ b : {b : A // b ≠ a}, Σ c : Third a b.val, Triple a b.val c.val
abbrev Cases (a : A) := EightRowCounting.Row8 a ⊕ EventualRowCounting.Extra a ⊕ Long a

def tripleEncode (a b c : A) (f : Triple a b c) :
    {z : A // z ∉ ({a,b,c} : Finset A)} → A := fun z => f.val z.val

omit [Fintype A] in
theorem tripleEncode_injective (a b c : A) : Function.Injective (tripleEncode a b c) := by
  intro f g h
  apply Subtype.ext
  funext z
  by_cases ha : z = a
  · subst z; exact f.property.1.trans g.property.1.symm
  by_cases hb : z = b
  · subst z; exact f.property.2.1.trans g.property.2.1.symm
  by_cases hc : z = c
  · subst z; exact f.property.2.2.trans g.property.2.2.symm
  exact congrFun h ⟨z, by simp [ha,hb,hc]⟩

theorem triple_bound (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fintype.card (Triple a b c) ≤ Fintype.card A ^ (Fintype.card A - 3) := by
  have hc : Fintype.card {z : A // z ∉ ({a,b,c} : Finset A)} = Fintype.card A - 3 := by
    have hh := Fintype.card_subtype_compl (fun z : A => z ∈ ({a,b,c} : Finset A))
    have hcard : ({a,b,c} : Finset A).card = 3 := by simp [hab,hac,hbc]
    simpa only [Fintype.card_coe,hcard] using hh
  simpa only [Fintype.card_fun,hc] using
    Fintype.card_le_of_injective (tripleEncode a b c) (tripleEncode_injective a b c)

def casesMap (a : A) : Cases a → EventualRowCounting.Row a
  | .inl f => EventualRowCounting.rowEncode a (.inl f)
  | .inr (.inl f) => EventualRowCounting.rowEncode a (.inr f)
  | .inr (.inr ⟨b,c,f⟩) => ⟨f.val, by rw [f.property.1,f.property.2.1,f.property.2.2]⟩

omit [Fintype A] in
theorem casesMap_surjective (a : A) : Function.Surjective (casesMap a) := by
  intro f
  by_cases ha : f.val (f.val a) = a
  · exact ⟨.inl ⟨f.val,ha⟩,rfl⟩
  have hb : f.val a ≠ a := by
    intro h
    apply ha
    rw [h,h]
  by_cases hc : f.val (f.val a) = f.val a
  · exact ⟨.inr (.inl ⟨⟨f.val a,hb⟩,⟨f.val,rfl,hc⟩⟩),rfl⟩
  · exact ⟨.inr (.inr ⟨⟨f.val a,hb⟩,
      ⟨f.val (f.val a),by simp [ha,hc]⟩,⟨f.val,rfl,rfl,f.property⟩⟩),rfl⟩

theorem long_bound (a : A) (hn : 3 ≤ Fintype.card A) :
    Fintype.card (Long a) ≤ Fintype.card A ^ (Fintype.card A - 1) := by
  let n := Fintype.card A
  calc
    _ = ∑ b : {b : A // b ≠ a}, ∑ c : Third a b.val, Fintype.card (Triple a b.val c.val) := by
      simp only [Long,Fintype.card_sigma]
    _ ≤ ∑ _b : {b : A // b ≠ a}, n * n ^ (n - 3) := by
      apply Finset.sum_le_sum
      intro b _
      calc
        _ ≤ ∑ _c : Third a b.val, n ^ (n - 3) := by
          apply Finset.sum_le_sum
          intro c _
          have hc := c.property
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
          exact triple_bound a b.val c.val b.property.symm (Ne.symm hc.1) (Ne.symm hc.2)
        _ ≤ n * n ^ (n - 3) := by
          simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
          exact Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)
    _ ≤ n * (n * n ^ (n - 3)) := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
      exact Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)
    _ = n ^ (n - 1) := by
      rw [← pow_succ',← pow_succ']
      congr 1
      omega

theorem row_bound (a : A) (hn : 3 ≤ Fintype.card A) :
    Fintype.card (EventualRowCounting.Row a) ≤ 4 * Fintype.card A ^ (Fintype.card A - 1) := by
  let n := Fintype.card A
  have hJ : (n - 1) * n ^ (n - 2) ≤ n ^ (n - 1) := by
    calc
      _ ≤ n * n ^ (n - 2) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = _ := by rw [← pow_succ']; congr 1; omega
  have hlong := long_bound a hn
  have hh := Fintype.card_le_of_surjective (casesMap a) (casesMap_surjective a)
  rw [Fintype.card_sum,Fintype.card_sum,EightRowCounting.card_row,
    EventualRowCounting.extra_count] at hh
  dsimp [n] at hJ
  omega

theorem upper_count (hn : 3 ≤ Fintype.card A) :
    Fintype.card {f : A → A → A // @Equation3253 A ⟨f⟩} ≤
      4 ^ Fintype.card A * (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Fintype.card_congr EventualRowCounting.tableEquiv,Fintype.card_pi,← mul_pow]
  calc
    _ ≤ ∏ _a : A, 4 * Fintype.card A ^ (Fintype.card A - 1) :=
      Finset.prod_le_prod (by intros; omega) (fun a _ => row_bound a hn)
    _ = _ := by simp

theorem upper_count_nat (hn : 3 ≤ Fintype.card A) :
    Nat.card {f : A → A → A // @Equation3253 A ⟨f⟩} ≤
      4 ^ Fintype.card A * (Fintype.card A ^ (Fintype.card A - 1)) ^ Fintype.card A := by
  rw [Nat.card_eq_fintype_card]
  exact upper_count hn

end EventualRowUpperCounting
