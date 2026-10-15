import equational_theories.Spectrum.Equation1483.OrderTwelve.NormalForm

/-! Lexicographic minimality of the complete second row under permutations
inside first-row fibers. Such permutations preserve the entire first row and
its image normalization. This strengthens the first-mention convention. -/
namespace Spectrum.E1483.OrderTwelve.SecondLexNormalization
open Magma.Central1483.CNF Spectrum.E1483.OrderTwelve.CNF
open Normalize Normalized Ranks Normalization RowOneNormalization HeadLexNormalization
abbrev A := Fin 12
abbrev Op := A → A → A

def swapRow (f : Op) (a b i : A) : A :=
  Equiv.swap a b (f 1 (Equiv.swap a b i))

def SecondLex (f : Op) (k : Nat) (zero : Bool) : Prop :=
  ∀ a b i : A, bound k zero < a.val → a < b →
    (¬ ∃ x, f x 0 = a) → (¬ ∃ x, f x 0 = b) → f 0 a = f 0 b →
    (∀ j : A, j < i → f 1 j = swapRow f a b j) →
    f 1 i ≤ swapRow f a b i

lemma firstMention_of_secondLex (f : Op) (k : Nat) (zero : Bool)
    (hl : SecondLex f k zero) : FirstMention f k zero := by
  intro a b i ha hab hia hca hcb hv hval
  by_contra hn
  have hp (j : A) (hj : j < i) : f 1 j = swapRow f a b j := by
    have hna : f 1 j ≠ a := fun he => hn ⟨j,hj,Or.inl he⟩
    have hnb : f 1 j ≠ b := fun he => hn ⟨j,hj,Or.inr he⟩
    simp only [swapRow,swap_fixed_lt a b j hab (hj.trans hia),
      Equiv.swap_apply_of_ne_of_ne hna hnb]
  have hh := hl a b i ha hab hca hcb hv hp
  simp only [swapRow,swap_fixed_lt a b i hab hia,hval,Equiv.swap_apply_right] at hh
  exact not_lt_of_ge hh hab

lemma refine_model (f : Op) (k : Nat) (zero : Bool)
    (h : RankCore f k zero) (hs : Sorted f k zero) (hk : 2 ≤ k) :
    ∃ g : Op, RankCore g k zero ∧ Sorted g k zero ∧
      (∀ x, g 0 x = f 0 x) ∧ FirstMention g k zero ∧ SecondLex g k zero := by
  classical
  let S : Set Op := {g | RankCore g k zero ∧ Sorted g k zero ∧ ∀ x, g 0 x = f 0 x}
  obtain ⟨g,hg,hmin⟩ := Set.exists_min_image S (fun q => toLex (q 1)) S.toFinite
    ⟨f,h,hs,fun _ => rfl⟩
  have hgg : RankCore g k zero ∧ Sorted g k zero ∧ ∀ x, g 0 x = f 0 x := hg
  have hl : SecondLex g k zero := by
    intro a b i ha hab hca hcb hv hpref
    let p := Equiv.swap a b
    let q := relabel g p
    obtain ⟨hc,hs',hr⟩ := swap_properties g k zero hgg.1 hgg.2.1 a b ha hab hca hcb hv
    have hq : q ∈ S := ⟨hc,hs',fun x => (hr x).trans (hgg.2.2 x)⟩
    have hbnd : 1 ≤ bound k zero := by cases zero <;> simp [bound] <;> omega
    have hp1 : p 1 = 1 := swap_fixed_lt a b 1 hab (by change 1 < a.val; omega)
    have hp1' : p.symm 1 = 1 := by apply p.injective; simpa using hp1.symm
    have hrow : q 1 = swapRow g a b := by
      funext j
      change p (g (p.symm 1) (p.symm j)) = Equiv.swap a b (g 1 (Equiv.swap a b j))
      rw [hp1']
      rfl
    have hh := hmin q hq
    rw [hrow] at hh
    exact Pi.apply_le_of_toLex hh hpref
  exact ⟨g,hgg.1,hgg.2.1,hgg.2.2,firstMention_of_secondLex g k zero hl,hl⟩

lemma refine_normalForm (f : Op) (k : Nat) (zero : Bool) (h : NormalForm f k zero) :
    ∃ g : Op, NormalForm g k zero ∧ (∀ x, g 0 x = f 0 x) ∧ SecondLex g k zero := by
  obtain ⟨g,hg,hs,hr,hm,hl⟩ := refine_model f k zero h.core h.sorted h.bounds.1
  refine ⟨g,⟨h.bounds,hg,hs,?_,?_,?_,hm⟩,hr,hl⟩
  · intro y
    rw [hr y]
    exact h.chain y
  · intro hz
    rw [hr 1]
    exact h.predecessor ((hr 0).symm.trans hz)
  · exact head_congr f g k zero h.headLex (fun x _ => hr x)

end Spectrum.E1483.OrderTwelve.SecondLexNormalization
