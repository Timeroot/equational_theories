import equational_theories.Parastrophes.Equation917SandwichCandidate

/-!
# A twenty-operation candidate for E917's finite left-division image

Write q(x)=(x*(x*x))*x, U(x)=x*q(x), and H(x,y)=q(x)*(x*y).
The identity is

    x = ((U(w)*(U(z)*y))*v) * H(x,(w*(z*y))*v).

Every image satisfies it. Conversely it forces surjective rows on arbitrary
carriers, and a quasigroup on finite carriers. The exact finite reduction is
to three permutations a,b,c satisfying

    U(x)*y=a(x*y),   x*a(y)=b(x*y),
    a(b(x))*y=c(x*y),   c(y)*H(x,y)=x.

The remaining assertion U=id is OPEN, so there is no characterization
attribute here. The companion affine file proves the full converse over all
commutative rings, including nilpotents and all characteristics.
-/
namespace Parastrophes.Eq917Image.DoubleUnitCandidate
open SandwichCandidate (U H F)

variable {A : Type} (D : Magma A)

def Identity : Prop := ∀ x y z w v,
  x = D.op (D.op (D.op (U D w) (D.op (U D z) y)) v)
    (H D x (D.op (D.op w (D.op z y)) v))

theorem of_basis (h : Basis D) : Identity D := by
  intro x y z w v
  have hu : U D z = z := (h.1 z).symm
  have hw : U D w = w := (h.1 w).symm
  rw [hu, hw]
  exact h.2 x _

theorem of_image (h : InImage Law917 .left D) : Identity D := by
  obtain ⟨M, hm, hd⟩ := h
  exact of_basis D (forward M D hd ((@Law917.models_iff A M).mp hm))

theorem rows_surjective (h : Identity D) : ∀ a, Function.Surjective (D.op a) := by
  have hs (y z w v : A) :
      Function.Surjective (D.op (D.op (D.op (U D w) (D.op (U D z) y)) v)) :=
    fun x => ⟨_, (h x y z w v).symm⟩
  intro t
  let a := D.op (U D t) (D.op (U D t) t)
  have hr : Function.Surjective (D.op (U D a)) := hs t t t (core D a)
  obtain ⟨v, hv⟩ := hr t
  obtain ⟨z, hz⟩ := hr (U D a)
  obtain ⟨y, hy⟩ := hr z
  simpa only [hy, hz, hv] using hs y a a v

theorem quasigroup [Finite A] (h : Identity D) : IsQuasigroup D := by
  have hq : IsSideQuasigroup .left D := fun x =>
    ⟨Finite.injective_iff_surjective.mpr (rows_surjective D h x),
      rows_surjective D h x⟩
  refine ⟨hq, fun t => ?_⟩
  letI : Nonempty A := ⟨t⟩
  classical
  let le (x : A) := Equiv.ofBijective (D.op x) (hq x)
  let j := D.op t (D.op t t)
  let k := D.op (U D t) (D.op (U D t) t)
  let s : A ≃ A := (le j).symm.trans (le k)
  have frame (x y : A) : D.op (s y) (H D x y) = x := by
    have he := (h x t t t ((le j).symm y)).symm
    change D.op ((le k) ((le j).symm y))
      (H D x ((le j) ((le j).symm y))) = x at he
    simpa only [(le j).apply_symm_apply] using he
  have col (x : A) : Function.Injective (fun y => D.op y x) := by
    intro y z he
    let u := D.op y x
    have hy : H D u (s.symm y) = x := by
      apply (hq y).1
      simpa only [s.apply_symm_apply] using frame u (s.symm y)
    have hz : H D u (s.symm z) = x := by
      apply (hq z).1
      simpa only [s.apply_symm_apply] using (frame u (s.symm z)).trans he
    have hh := ((hq (core D u)).1.comp (hq u).1) (hy.trans hz.symm)
    exact s.symm.injective hh
  exact ⟨col t, Finite.surjective_of_injective (col t)⟩

theorem reduction [Finite A] [Nonempty A] (h : Identity D) :
    ∃ a b c : A ≃ A,
      (∀ x y, D.op (U D x) y = a (D.op x y)) ∧
      (∀ x y, D.op x (a y) = b (D.op x y)) ∧
      (∀ x y, D.op (a (b x)) y = c (D.op x y)) ∧
      (∀ x y, D.op (c y) (H D x y) = x) := by
  classical
  let o : A := Classical.choice inferInstance
  have hq := quasigroup D h
  let le (x : A) := Equiv.ofBijective (D.op x) (hq.1 x)
  let re (x : A) := Equiv.ofBijective (fun y => D.op y x) (hq.2 x)
  let j := D.op o (D.op o o)
  let k := D.op (U D o) (D.op (U D o) o)
  let c : A ≃ A := (le j).symm.trans (le k)
  have frame (x y : A) : D.op (c y) (H D x y) = x := by
    have he := (h x o o o ((le j).symm y)).symm
    change D.op ((le k) ((le j).symm y))
      (H D x ((le j) ((le j).symm y))) = x at he
    simpa only [(le j).apply_symm_apply] using he
  have comparison (y z w v : A) :
      D.op (D.op (U D w) (D.op (U D z) y)) v =
        c (D.op (D.op w (D.op z y)) v) := by
    apply (hq.2 (H D o (D.op (D.op w (D.op z y)) v))).1
    exact (h o y z w v).symm.trans (frame o _).symm
  let g : A ≃ A := (re o).trans (c.trans (re o).symm)
  have middle (z y w : A) : D.op (U D w) (D.op (U D z) y) =
      g (D.op w (D.op z y)) := by
    apply (re o).injective
    change D.op (D.op (U D w) (D.op (U D z) y)) o =
      (re o) ((re o).symm (c ((re o) (D.op w (D.op z y)))))
    rw [(re o).apply_symm_apply]
    exact comparison y z w o
  let a : A ≃ A := (le o).trans (g.trans (le (U D o)).symm)
  have first (x y : A) : D.op (U D x) y = a (D.op x y) := by
    apply (le (U D o)).injective
    change D.op (U D o) (D.op (U D x) y) =
      (le (U D o)) ((le (U D o)).symm (g ((le o) (D.op x y))))
    rw [(le (U D o)).apply_symm_apply]
    exact middle x y o
  let b : A ≃ A := g.trans a.symm
  have ab (x : A) : a (b x) = g x := a.apply_symm_apply _
  have second (x y : A) : D.op x (a y) = b (D.op x y) := by
    obtain ⟨z, rfl⟩ := (hq.1 o).2 y
    apply a.injective
    rw [ab, ← first, ← first]
    exact middle o z x
  have third (x y : A) : D.op (a (b x)) y = c (D.op x y) := by
    rw [ab]
    obtain ⟨z, rfl⟩ := (hq.1 o).2 x
    obtain ⟨t, rfl⟩ := (hq.1 o).2 z
    rw [← middle]
    exact comparison t o o y
  exact ⟨a, b, c, first, second, third, frame⟩

theorem of_reduction (a b c : A → A)
    (ha : ∀ x y, D.op (U D x) y = a (D.op x y))
    (hb : ∀ x y, D.op x (a y) = b (D.op x y))
    (hc : ∀ x y, D.op (a (b x)) y = c (D.op x y))
    (hf : ∀ x y, D.op (c y) (H D x y) = x) : Identity D := by
  intro x y z w v
  rw [ha, ha, hb, hc, hf]

theorem unit_bijective [Finite A] (h : Identity D) : Function.Bijective (U D) := by
  have hi : Function.Injective (U D) := by
    intro x y he
    letI : Nonempty A := ⟨x⟩
    obtain ⟨a, _, _, ha, _, _, _⟩ := reduction D h
    apply ((quasigroup D h).2 x).1
    change D.op x x = D.op y x
    apply a.injective
    rw [← ha, ← ha, he]
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- The commutations used in normalized searches are consequences of the
reduction, not additional restrictions on the candidate. -/
theorem commuting_maps (a b c : A → A) (hq : IsQuasigroup D)
    (ha : ∀ x y, D.op (U D x) y = a (D.op x y))
    (hb : ∀ x y, D.op x (a y) = b (D.op x y))
    (hc : ∀ x y, D.op (a (b x)) y = c (D.op x y)) :
    Function.Commute a b ∧ Function.Commute b c := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := (hq.1 x).2 x
    have he : D.op (U D x) (a y) = D.op (U D x) (a y) := rfl
    conv_lhs at he => rw [ha, hb]
    conv_rhs at he => rw [hb, ha]
    simpa only [hy] using he
  · intro x
    obtain ⟨y, hy⟩ := (hq.1 x).2 x
    have he : D.op (a (b x)) (a y) = D.op (a (b x)) (a y) := rfl
    conv_lhs at he => rw [hc, hb]
    conv_rhs at he => rw [hb, hc]
    simpa only [hy] using he.symm

/-- A period of U at one point is a period everywhere. Thus a nontrivial
U consists of equal-length cycles; this justifies fixing its cycle form in
finite model searches. -/
theorem unit_iterate_fixed [Finite A] (h : Identity D) (n : ℕ) (o : A)
    (ho : (U D)^[n] o = o) : ∀ x, (U D)^[n] x = x := by
  letI : Nonempty A := ⟨o⟩
  obtain ⟨a, _, _, ha, _, _, _⟩ := reduction D h
  have hq := quasigroup D h
  have step (k : ℕ) (x y : A) : D.op ((U D)^[k] x) y = (a : A → A)^[k] (D.op x y) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply', ha, ih]
  have aid (x : A) : (a : A → A)^[n] x = x := by
    obtain ⟨y, rfl⟩ := (hq.1 o).2 x
    exact (step n o y).symm.trans (by rw [ho])
  intro x
  apply (hq.2 o).1
  change D.op ((U D)^[n] x) o = D.op x o
  rw [step, aid]

/-- One fixed point suffices, but its existence is still unproved. -/
theorem basis_of_fixed_point [Finite A] (h : Identity D) (o : A)
    (ho : U D o = o) : Basis D := by
  have hu : ∀ x, U D x = x := by
    simpa only [Function.iterate_one] using unit_iterate_fixed D h 1 o ho
  have hq := quasigroup D h
  constructor
  · intro x
    exact (hu x).symm
  · intro x y
    obtain ⟨v, hv⟩ := (hq.1 (D.op o (D.op o o))).2 y
    have he := h x o o o v
    simpa only [hu, hv] using he

end Parastrophes.Eq917Image.DoubleUnitCandidate
