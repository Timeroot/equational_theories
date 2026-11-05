import equational_theories.Parastrophes.Equation917ImageBasis

/-!
# A sandwich candidate for the finite E917 division image

Write q(x)=(x*(x*x))*x, U(x)=x*q(x), H(x,y)=q(x)*(x*y),
F(x,y)=y*H(x,y), and G(y,x)=H(y*x,y). The proposed identity is

    x = y * F(H(G(z,U(x)),y),w).

Every actual image satisfies it. Conversely, on finite carriers it forces
bijective rows, a bijective U, and common permutations a(x)=F(x,y) and
b(x)=G(y,x). It even forces bijective columns. These reductions are proved
below; they do NOT yet prove that a and U are identity maps. Consequently
there is no characterization attribute on this file.

The expanded identity has 782 operations. Named subterms make the checked
reduction small; no finite table or external solver certificate is used.
-/
namespace Parastrophes.Eq917Image.SandwichCandidate

variable {A : Type} (D : Magma A)

def U (x : A) := D.op x (core D x)
def H (x y : A) := D.op (core D x) (D.op x y)
def F (x y : A) := D.op y (H D x y)
def G (y x : A) := H D (D.op y x) y
def Identity : Prop := ∀ x y z w, x = D.op y (F D (H D (G D z (U D x)) y) w)

theorem of_basis (h : Basis D) (hq : IsSideQuasigroup .left D) : Identity D := by
  have hu (x) : U D x = x := (h.1 x).symm
  have hf (x y) : F D x y = x := (h.2 x y).symm
  have hg (y x) : G D y x = x := by
    apply (hq y).1
    exact hf (D.op y x) y
  intro x y z w
  rw [hu, hg, hf]
  exact h.2 x y

theorem of_image (h : InImage Law917 .left D) : Identity D := by
  obtain ⟨M, hM, hd⟩ := h
  exact of_basis D (forward M D hd ((@Law917.models_iff A M).mp hM))
    (sideQuasigroup_of_division (division_symm hd))

theorem rows [Finite A] (h : Identity D) : IsSideQuasigroup .left D := by
  intro y
  have hs : Function.Surjective (D.op y) := fun x =>
    ⟨F D (H D (G D y (U D x)) y) y, (h x y y y).symm⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem unit_bijective [Finite A] (h : Identity D) : Function.Bijective (U D) := by
  have hi : Function.Injective (U D) := by
    intro x y he
    exact (h x x x x).trans ((congrArg (fun t =>
      D.op x (F D (H D (G D x t) x) x)) he).trans (h y x x x).symm)
  exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

theorem rows_of_unit_surjective (h : Identity D) (hu : Function.Surjective (U D)) :
    IsSideQuasigroup .left D := by
  intro z
  constructor
  · intro x y he
    obtain ⟨x', rfl⟩ := hu x
    obtain ⟨y', rfl⟩ := hu y
    have hg : G D z (U D x') = G D z (U D y') := congrArg (fun t => H D t z) he
    have hh := (h x' z z z).trans ((congrArg (fun t =>
      D.op z (F D (H D t z) z)) hg).trans (h y' z z z).symm)
    exact congrArg (U D) hh
  · intro x
    exact ⟨_, (h x z z z).symm⟩

/-- Finiteness is only needed to supply surjectivity of U. This stronger
version is useful, for example, for affine operations on infinite rings. -/
theorem common_maps_of_unit_surjective [Nonempty A] (h : Identity D)
    (hu : Function.Surjective (U D)) :
    ∃ a b : A → A, Function.Bijective a ∧ Function.Bijective b ∧
      (∀ x y, F D x y = a x) ∧ (∀ y x, G D y x = b x) ∧
      (∀ x y, D.op y (a (H D (b (U D x)) y)) = x) := by
  classical
  let o : A := Classical.choice inferInstance
  have hq := rows_of_unit_surjective D h hu
  have hH (x : A) : Function.Bijective (H D x) := (hq (core D x)).comp (hq x)
  let a := fun x => F D x o
  have hf (x w) : F D x w = a x := by
    obtain ⟨y, hy⟩ := (hH (G D o (U D o))).2 x
    have he := (hq y).1 ((h o y o w).symm.trans (h o y o o))
    simpa only [hy] using he
  have hgi (z : A) : Function.Injective (G D z) := by
    intro x y he
    obtain ⟨x', rfl⟩ := hu x
    obtain ⟨y', rfl⟩ := hu y
    have hh : x' = y' := (h x' o z o).trans ((congrArg (fun t =>
      D.op o (F D (H D t o) o)) he).trans (h y' o z o).symm)
    exact congrArg (U D) hh
  have hab (x y) : a (D.op x y) = D.op x (G D x y) := (hf _ x).symm
  have hai : Function.Injective a := by
    intro x y he
    obtain ⟨x', rfl⟩ := (hq o).2 x
    obtain ⟨y', rfl⟩ := (hq o).2 y
    rw [hab, hab] at he
    exact congrArg (D.op o) (hgi o ((hq o).1 he))
  have hcol (y : A) : Function.Injective (fun x => H D x y) := by
    intro x z he
    apply hai
    rw [← hf x y, ← hf z y]
    exact congrArg (D.op y) he
  let b := G D o
  have hg (z x) : G D z x = b x := by
    obtain ⟨x', rfl⟩ := hu x
    have he := (hq o).1 ((h x' o z o).symm.trans (h x' o o o))
    rw [hf, hf] at he
    exact hcol o (hai he)
  have has : Function.Surjective a := by
    intro t
    refine ⟨H D (G D o (U D (D.op o t))) o, ?_⟩
    exact (hq o).1 (h (D.op o t) o o o).symm
  have hbs : Function.Surjective b := by
    intro t
    obtain ⟨x, hx⟩ := has (D.op o t)
    obtain ⟨y, rfl⟩ := (hq o).2 x
    exact ⟨y, (hq o).1 ((hab o y).symm.trans hx)⟩
  refine ⟨a, b, ⟨hai, has⟩, ⟨hgi o, hbs⟩, hf, hg, ?_⟩
  intro x y
  simpa only [hf, hg] using (h x y o o).symm

theorem common_maps [Finite A] [Nonempty A] (h : Identity D) :
    ∃ a b : A → A, Function.Bijective a ∧ Function.Bijective b ∧
      (∀ x y, F D x y = a x) ∧ (∀ y x, G D y x = b x) ∧
      (∀ x y, D.op y (a (H D (b (U D x)) y)) = x) :=
  common_maps_of_unit_surjective D h (unit_bijective D h).2

theorem quasigroup_of_unit_surjective (h : Identity D)
    (hu : Function.Surjective (U D)) : IsQuasigroup D := by
  have hq := rows_of_unit_surjective D h hu
  refine ⟨hq, fun y => ?_⟩
  letI : Nonempty A := ⟨y⟩
  obtain ⟨a, _, ha, _, hf, _, _⟩ := common_maps_of_unit_surjective D h hu
  have hi : Function.Injective (fun x => D.op x y) := by
    intro x z he
    obtain ⟨t, ht⟩ := ha.2 (D.op x y)
    have hx : H D t x = y := (hq x).1 ((hf t x).trans ht)
    have hz : H D t z = y := (hq z).1 ((hf t z).trans (ht.trans he))
    exact ((hq (core D t)).1.comp (hq t).1) (hx.trans hz.symm)
  refine ⟨hi, fun t => ?_⟩
  obtain ⟨z, hz⟩ := ha.2 t
  obtain ⟨x, hx⟩ := ((hq (core D z)).comp (hq z)).2 y
  exact ⟨x, (congrArg (D.op x) hx).symm.trans ((hf z x).trans hz)⟩

theorem quasigroup [Finite A] (h : Identity D) : IsQuasigroup D :=
  quasigroup_of_unit_surjective D h (unit_bijective D h).2

end Parastrophes.Eq917Image.SandwichCandidate
