import equational_theories.Parastrophes.Equation917SandwichCandidate

/-!
# An E917 compression reduced to two permutations

This is an OPEN candidate, not a characterization. With the existing terms
`U(x)=x*q(x)`, `F(x,y)=y*(q(x)*(x*y))`, and
`G(y,x)=q(y*x)*((y*x)*y)`, consider the composition F² G⁴ U, with independent
parameters for all six binary terms. Every actual division image satisfies it.

On a finite carrier the composition identity forces every factor to be a
permutation. Independence of the parameters then makes F(x,y)=a(x) and
G(y,x)=b(x). The operation is a quasigroup, each row conjugates b to a, and
the sole remaining composition condition is a² b⁴ U=id. No commutation of
a and b is assumed or proved. A fixed point of either map would finish the
converse, but its existence remains open.

The choice of exponents comes from the scalar affine obstruction: the relevant
integer resultant is 4³-4*3²-3³=1. This motivates the candidate but is not a
proof for arbitrary magmas. Expanding the terms gives 101536 operations;
all reductions here use named subterms and require no such expansion.
-/
namespace Parastrophes.Eq917Image.CompositionCandidate
open SandwichCandidate (U H F G)

variable {A : Type} (D : Magma A)

def Identity : Prop := ∀ x y z r s t v,
  F D (F D (G D r (G D s (G D t (G D v (U D x))))) z) y = x

theorem of_image (h : InImage Law917 .left D) : Identity D := by
  obtain ⟨M, hm, hd⟩ := h
  have hb := forward M D hd ((@Law917.models_iff A M).mp hm)
  have hq := sideQuasigroup_of_division (division_symm hd)
  have hf (x y) : F D x y = x := (hb.2 x y).symm
  have hg (y x) : G D y x = x := by
    apply (hq y).1
    exact hf (D.op y x) y
  have hu (x) : U D x = x := (hb.1 x).symm
  intro x y z r s t v
  simp only [hu, hg, hf]

theorem unit_bijective [Finite A] (h : Identity D) : Function.Bijective (U D) := by
  have hi : Function.Injective (U D) := by
    intro x y he
    have hh := congrArg (fun u =>
      F D (F D (G D x (G D x (G D x (G D x u)))) x) x) he
    exact (h x x x x x x x).symm.trans (hh.trans (h y x x x x x x))
  exact ⟨hi, Finite.surjective_of_injective hi⟩

theorem F_bijective [Finite A] (h : Identity D) (y : A) :
    Function.Bijective (fun x => F D x y) := by
  have hs : Function.Surjective (fun x => F D x y) := fun x =>
    ⟨F D (G D y (G D y (G D y (G D y (U D x))))) y, h x y y y y y y⟩
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem G_bijective [Finite A] (h : Identity D) (z : A) :
    Function.Bijective (G D z) := by
  have hu := unit_bijective D h
  have hi : Function.Injective (G D z) := by
    intro x y he
    obtain ⟨x', rfl⟩ := hu.2 x
    obtain ⟨y', rfl⟩ := hu.2 y
    have hh := congrArg (fun u =>
      F D (F D (G D z (G D z (G D z u))) z) z) he
    have hxy : x' = y' := (h x' z z z z z z).symm.trans
      (hh.trans (h y' z z z z z z))
    exact congrArg (U D) hxy
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- The reduction retains the precise order of composition. -/
theorem common_maps [Finite A] (h : Identity D) (o : A) :
    ∃ a b : A → A, Function.Bijective a ∧ Function.Bijective b ∧
      (∀ x y, F D x y = a x) ∧ (∀ y x, G D y x = b x) ∧
      (∀ x, a (a (b (b (b (b (U D x)))))) = x) := by
  let a := fun x => F D x o
  let b := G D o
  have hu := unit_bijective D h
  have ha := F_bijective D h o
  have hb := G_bijective D h o
  have tail : Function.Surjective (fun x =>
      F D (G D o (G D o (G D o (G D o (U D x))))) o) :=
    ha.2.comp (hb.2.comp (hb.2.comp (hb.2.comp (hb.2.comp hu.2))))
  have hf (x y) : F D x y = a x := by
    obtain ⟨t, rfl⟩ := tail x
    exact (h t y o o o o o).trans (h t o o o o o o).symm
  have hg (y x) : G D y x = b x := by
    obtain ⟨t, rfl⟩ := hu.2 x
    have he := (h t o o o o o y).trans (h t o o o o o o).symm
    exact hb.1 (hb.1 (hb.1 (ha.1 (ha.1 he))))
  refine ⟨a, b, ha, hb, hf, hg, ?_⟩
  intro x
  simpa only [hf, hg] using h x o o o o o o

theorem quasigroup [Finite A] (h : Identity D) : IsQuasigroup D := by
  have rows : IsSideQuasigroup .left D := by
    intro y
    have hs : Function.Surjective (D.op y) := by
      intro x
      obtain ⟨z, hz⟩ := (F_bijective D h y).2 x
      exact ⟨H D z y, hz⟩
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  refine ⟨rows, fun y => ?_⟩
  obtain ⟨a, _, ha, _, hf, _, _⟩ := common_maps D h y
  have hi : Function.Injective (fun x => D.op x y) := by
    intro x z he
    obtain ⟨t, ht⟩ := ha.2 (D.op x y)
    have hx : H D t x = y := (rows x).1 ((hf t x).trans ht)
    have hz : H D t z = y := (rows z).1 ((hf t z).trans (ht.trans he))
    exact ((rows (core D t)).1.comp (rows t).1) (hx.trans hz.symm)
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- A row conjugacy with a fixed output point is trivial. This needs no
finiteness or special E917 identities. -/
theorem shifts_trivial_of_fixed (a b : A → A) (hq : IsQuasigroup D)
    (shift : ∀ x y, D.op x (b y) = a (D.op x y))
    (o : A) (ho : a o = o) : (∀ x, a x = x) ∧ (∀ x, b x = x) := by
  have bid (y : A) : b y = y := by
    obtain ⟨x, hx⟩ := (hq.2 y).2 o
    change D.op x y = o at hx
    apply (hq.1 x).1
    rw [shift, hx, ho]
  refine ⟨?_, bid⟩
  intro x
  obtain ⟨y, rfl⟩ := (hq.1 o).2 x
  rw [← shift, bid]

/-- In particular, any power fixing one point is the identity everywhere.
This justifies using uniform cycle lengths in finite countermodel searches. -/
theorem shifts_iterate_fixed (a b : A → A) (hq : IsQuasigroup D)
    (shift : ∀ x y, D.op x (b y) = a (D.op x y))
    (n : ℕ) (o : A) (ho : (a^[n]) o = o) :
    (∀ x, (a^[n]) x = x) ∧ (∀ x, (b^[n]) x = x) := by
  apply shifts_trivial_of_fixed D (a^[n]) (b^[n]) hq _ o ho
  clear ho
  intro x y
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', shift, ih]

/-- Two instances of the common identities compare the core-square map
with the ordinary square. This does not assume either map is the identity. -/
theorem core_square_iff_maps_agree (a b : A → A) (hq : IsQuasigroup D)
    (hf : ∀ x y, F D x y = a x) (hg : ∀ y x, G D y x = b x) (x : A) :
    core D (core D x) = D.op x x ↔ a x = b x := by
  let t := D.op (core D x) (D.op x (D.op x x))
  have ha : D.op (D.op x x) t = a x := hf x (D.op x x)
  have hb : D.op (core D (core D x)) t = b x :=
    hg (D.op x (D.op x x)) x
  constructor
  · intro he
    rw [he] at hb
    exact ha.symm.trans hb
  · intro he
    exact (hq.2 t).1 (hb.trans (he.symm.trans ha.symm))

/-- If U=id, agreement of a and b at even one point suffices. In particular,
in the involution search the matching pair a(0)=b(0) can be ruled out by this
proof rather than by another finite-model certificate. -/
theorem maps_trivial_of_unit_and_agreement (a b : A → A) (hq : IsQuasigroup D)
    (hf : ∀ x y, F D x y = a x) (hg : ∀ y x, G D y x = b x)
    (hu : ∀ x, U D x = x) (o : A) (ho : a o = b o) :
    (∀ x, a x = x) ∧ (∀ x, b x = x) := by
  have hs := (core_square_iff_maps_agree D a b hq hf hg o).mpr ho
  have hu' := hu (core D o)
  change D.op (core D o) (core D (core D o)) = core D o at hu'
  rw [hs] at hu'
  have hao : a o = o := by
    rw [← hf o o]
    change D.op o (D.op (core D o) (D.op o o)) = o
    rw [hu']
    exact hu o
  apply shifts_trivial_of_fixed D a b hq _ o hao
  intro x y
  rw [← hg x y]
  exact hf (D.op x y) x

/-- Conjugacy makes b an involution whenever a is one. The original
composition then reduces to U=id, with no commutation assumption. -/
theorem unit_of_involutions (a b : A → A) (hq : IsQuasigroup D)
    (h : Identity D) (hf : ∀ x y, F D x y = a x)
    (hg : ∀ y x, G D y x = b x) (ha : ∀ x, a (a x) = x) :
    ∀ x, U D x = x := by
  have shift (x y) : D.op x (b y) = a (D.op x y) := by
    rw [← hg x y]
    exact hf (D.op x y) x
  have hb (x) : b (b x) = x := by
    apply (hq.1 x).1
    rw [shift, shift, ha]
  intro x
  simpa only [hf, hg, ha, hb] using h x x x x x x x

/-- The still-missing fixed point is sufficient for the unrestricted finite
converse. This theorem is conditional and has no catalogue attribute. -/
theorem basis_of_fixed_point [Finite A] (h : Identity D) (o : A)
    (ho : F D o o = o) : Basis D := by
  obtain ⟨a, b, _, _, hf, hg, hu⟩ := common_maps D h o
  have shift (x y) : D.op x (b y) = a (D.op x y) := by
    rw [← hg x y]
    exact hf (D.op x y) x
  obtain ⟨aid, bid⟩ := shifts_trivial_of_fixed D a b (quasigroup D h) shift o
    ((hf o o).symm.trans ho)
  constructor
  · intro x
    simpa only [aid, bid] using (hu x).symm
  · intro x y
    exact ((hf x y).trans (aid x)).symm

/-- If the two common maps coincide, their action on the core has weight two,
and the map itself has fourth power one. These are quasigroup calculations,
without a finiteness assumption or the composition identity. -/
theorem equal_maps_algebra (a : A → A) (ha : Function.Bijective a)
    (hq : IsQuasigroup D) (hf : ∀ x y, F D x y = a x)
    (hg : ∀ y x, G D y x = a x) :
    (∀ x y, D.op x (a y) = a (D.op x y)) ∧
    (∀ x, core D (a x) = a (a (core D x))) ∧
    (∀ x, a (a (a (a x))) = x) := by
  classical
  let ae := Equiv.ofBijective a ha
  let ai := ae.symm
  have aai (x) : a (ai x) = x := ae.apply_symm_apply x
  have aia (x) : ai (a x) = x := ae.symm_apply_apply x
  have second (x y) : D.op x (a y) = a (D.op x y) := by
    rw [← hg x y]
    exact hf (D.op x y) x
  have hH (x y) : H D x (a y) = a (H D x y) := by
    unfold H
    rw [second, second]
  have invariant (x y) : D.op (a x) (a y) = D.op x y := by
    obtain ⟨t, ht⟩ := ha.2 (D.op x y)
    have hy : H D t x = y := (hq.1 x).1 ((hf t x).trans ht)
    have hh := hf t (a x)
    change D.op (a x) (H D t (a x)) = a t at hh
    rwa [hH, hy, ht] at hh
  have first (x y) : D.op (a x) y = ai (D.op x y) := by
    apply ha.1
    rw [← second, invariant, aai]
  have inverse_first (x y) : D.op (ai x) y = a (D.op x y) := by
    have hh := invariant (ai x) y
    rw [aai, second] at hh
    exact hh.symm
  have qshift (x) : core D (a x) = a (a (core D x)) := by
    unfold core
    rw [invariant, first, inverse_first, second]
  have weight (x y) : a (a (a (H D (a x) y))) = H D x y := by
    unfold H
    rw [qshift, first, first, aai, aai, ← second, ← second, invariant]
  refine ⟨second, qshift, ?_⟩
  intro x
  apply ha.1
  have hh := congrArg (D.op x) (weight x x)
  rw [second, second, second] at hh
  change a (a (a (F D (a x) x))) = F D x x at hh
  simpa only [hf] using hh

/-- Equality of the common maps suffices for the unrestricted finite converse.
Equivalently, the additional core-square identity suffices. Equality of the
maps is still an explicit hypothesis here, not an asserted consequence. -/
theorem basis_of_equal_maps [Finite A] (h : Identity D) (a : A → A)
    (ha : Function.Bijective a) (hf : ∀ x y, F D x y = a x)
    (hg : ∀ y x, G D y x = a x) : Basis D := by
  have hq := quasigroup D h
  obtain ⟨second, _, fourth⟩ := equal_maps_algebra D a ha hq hf hg
  have hu (x) : U D x = a (a x) := by
    have hh := h x x x x x x x
    simp only [hf, hg, fourth] at hh
    have he := congrArg (fun t => a (a t)) hh
    simpa only [fourth] using he
  have aid (x) : a x = x := by
    have hs := (core_square_iff_maps_agree D a a hq hf hg x).mpr rfl
    calc
      a x = F D x x := (hf x x).symm
      _ = D.op x (U D (core D x)) := by simp only [F, H, U, hs]
      _ = a (a (U D x)) := by rw [hu, second, second]; rfl
      _ = x := by rw [hu, fourth]
  constructor
  · intro x
    exact ((hu x).trans ((congrArg a (aid x)).trans (aid x))).symm
  · intro x y
    exact ((hf x y).trans (aid x)).symm

end Parastrophes.Eq917Image.CompositionCandidate
