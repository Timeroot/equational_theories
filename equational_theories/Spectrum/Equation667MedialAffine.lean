import equational_theories.Spectrum.Equation667AffineThree

/-! A direct Toyoda representation for finite medial E667 magmas. Normalize
at one point to obtain a loop. Mediality makes its left translations commute,
so the loop is an abelian group; the original translations become affine. -/
namespace Spectrum.E667.MedialAffine
noncomputable section
open Equiv
variable {Q : Type*} [Magma Q] [Finite Q]

def left (h : Equation667 Q) (a : Q) : Perm Q :=
  Equiv.ofBijective (fun x => a ◇ x)
    ⟨E667883.left_injective667 h a,
      Finite.injective_iff_surjective.mp (E667883.left_injective667 h a)⟩

def right (h : Equation667 Q) (a : Q) : Perm Q :=
  Equiv.ofBijective (fun x => x ◇ a)
    ⟨E667883.right_injective667 h a,
      Finite.injective_iff_surjective.mp (E667883.right_injective667 h a)⟩

abbrev Medial : Prop := ∀ x y z w : Q, (x ◇ y) ◇ (z ◇ w) = (x ◇ z) ◇ (y ◇ w)

theorem row_medial (h : Equation667 Q) (hm : Medial (Q := Q)) (x y z : Q) :
    left h (x ◇ y) * left h z = left h (x ◇ z) * left h y := by
  ext w
  exact hm x y z w

/-- Normalized left translations commute. Three instances of mediality
give this identity without any assumption about idempotents. -/
theorem rows_commute (h : Equation667 Q) (hm : Medial (Q := Q)) (a x y : Q) :
    left h x * (left h a)⁻¹ * left h y = left h y * (left h a)⁻¹ * left h x := by
  let u := (left h a).symm x
  let v := (left h a).symm y
  let w := (left h a).symm a
  have hu : a ◇ u = x := (left h a).apply_symm_apply x
  have hv : a ◇ v = y := (left h a).apply_symm_apply y
  have hw : a ◇ w = a := (left h a).apply_symm_apply a
  have h1 := row_medial h hm a u v
  have h2 := row_medial h hm a v w
  have h3 := row_medial h hm a u w
  rw [hu,hv] at h1
  rw [hv,hw] at h2
  rw [hu,hw] at h3
  apply mul_right_cancel (b := left h w)
  calc
    _ = left h x * ((left h a)⁻¹ * (left h y * left h w)) := by group
    _ = left h x * left h v := by rw [h2]; group
    _ = left h y * left h u := h1
    _ = left h y * ((left h a)⁻¹ * (left h x * left h w)) := by rw [h3]; group
    _ = _ := by group

def plus (h : Equation667 Q) (a x y : Q) : Q :=
  (right h a).symm x ◇ (left h a).symm y

theorem zero_plus (h : Equation667 Q) (a x : Q) : plus h a (a ◇ a) x = x := by
  have ha : (right h a).symm (a ◇ a) = a := (right h a).symm_apply_apply a
  rw [plus,ha]
  exact (left h a).apply_symm_apply x

theorem plus_zero (h : Equation667 Q) (a x : Q) : plus h a x (a ◇ a) = x := by
  have ha : (left h a).symm (a ◇ a) = a := (left h a).symm_apply_apply a
  rw [plus,ha]
  exact (right h a).apply_symm_apply x

theorem plus_left_comm (h : Equation667 Q) (hm : Medial (Q := Q)) (a x y z : Q) :
    plus h a x (plus h a y z) = plus h a y (plus h a x z) := by
  exact congrArg (fun E : Perm Q => E ((left h a).symm z))
    (rows_commute h hm a ((right h a).symm x) ((right h a).symm y))

theorem plus_comm (h : Equation667 Q) (hm : Medial (Q := Q)) (a x y : Q) :
    plus h a x y = plus h a y x := by
  simpa only [plus_zero] using plus_left_comm h hm a x y (a ◇ a)

theorem plus_assoc (h : Equation667 Q) (hm : Medial (Q := Q)) (a x y z : Q) :
    plus h a (plus h a x y) z = plus h a x (plus h a y z) := by
  rw [plus_comm h hm a (plus h a x y) z, plus_left_comm h hm a,
    plus_comm h hm a z y]

def plusLeft (h : Equation667 Q) (a x : Q) : Perm Q :=
  (left h a).symm.trans (left h ((right h a).symm x))

@[reducible] def group (h : Equation667 Q) (hm : Medial (Q := Q)) (a : Q) : AddCommGroup Q := by
  letI : Add Q := ⟨plus h a⟩
  letI : Zero Q := ⟨a ◇ a⟩
  letI : Neg Q := ⟨fun x => (plusLeft h a x).symm (a ◇ a)⟩
  exact {
  add := plus h a
  zero := a ◇ a
  neg x := (plusLeft h a x).symm (a ◇ a)
  add_assoc := plus_assoc h hm a
  zero_add := zero_plus h a
  add_zero := plus_zero h a
  neg_add_cancel x := by
    change plus h a ((plusLeft h a x).symm (a ◇ a)) x = a ◇ a
    rw [plus_comm h hm]
    exact (plusLeft h a x).apply_symm_apply (a ◇ a)
  add_comm := plus_comm h hm a
  nsmul := nsmulRec
  zsmul := zsmulRec }

theorem representation (h : Equation667 Q) (hm : Medial (Q := Q)) (a : Q) :
    letI := group h hm a
    ∃ f g : AddMonoid.End Q, ∃ c : Q,
      ∀ x y : Q, x ◇ y = AffineStructure.op f g c x y := by
  letI := group h hm a
  let f := right h a
  let g := left h a
  have ha : a ◇ a = (0 : Q) := rfl
  have hf : f a = 0 := rfl
  have hg : g a = 0 := rfl
  have hop (x y : Q) : x ◇ y = f x + g y := by
    change x ◇ y = (right h a).symm (f x) ◇ (left h a).symm (g y)
    rw [(right h a).symm_apply_apply, (left h a).symm_apply_apply]
  have hm' (x y z w : Q) :
      f (f x+g y)+g (f z+g w) = f (f x+g z)+g (f y+g w) := by
    simpa only [hop] using hm x y z w
  have fadd (x y : Q) : f (x+y) = f x+f y-f 0 := by
    obtain ⟨u,rfl⟩ := f.surjective x
    obtain ⟨v,rfl⟩ := g.surjective y
    have h1 := hm' u v a a
    have h2 := hm' a v a a
    simp only [hf,hg,add_zero,zero_add] at h1 h2
    calc
      f (f u+g v) = (f (f u+g v)+g 0)-(f (g v)+g 0)+f (g v) := by abel
      _ = (f (f u)+g (f v))-(f 0+g (f v))+f (g v) := by rw [h1,h2]
      _ = _ := by abel
  have gadd (x y : Q) : g (x+y) = g x+g y-g 0 := by
    obtain ⟨u,rfl⟩ := f.surjective x
    obtain ⟨v,rfl⟩ := g.surjective y
    have h1 := hm' a a u v
    have h2 := hm' a a u a
    simp only [hf,hg,add_zero,zero_add] at h1 h2
    calc
      g (f u+g v) = (f 0+g (f u+g v))-(f 0+g (f u))+g (f u) := by abel
      _ = (f (g u)+g (g v))-(f (g u)+g 0)+g (f u) := by rw [h1,h2]
      _ = _ := by abel
  let F : AddMonoid.End Q := {
    toFun := fun x => f x-f 0
    map_zero' := sub_self _
    map_add' := fun x y => by rw [fadd]; abel }
  let G : AddMonoid.End Q := {
    toFun := fun x => g x-g 0
    map_zero' := sub_self _
    map_add' := fun x y => by rw [gadd]; abel }
  refine ⟨F,G,f 0+g 0,?_⟩
  intro x y
  change x ◇ y = (f x-f 0)+(g y-g 0)+(f 0+g 0)
  rw [hop]
  abel

/-- Every root obstruction for the affine coefficient polynomial applies to
all finite medial E667 magmas, regardless of their original presentation. -/
theorem prime_square_dvd [Nonempty Q] (h : Equation667 Q) (hm : Medial (Q := Q))
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card Q)
    (hr : ∀ t : ZMod p, t^8-t^6-t^4-1 ≠ 0) : p^2 ∣ Nat.card Q := by
  obtain ⟨a⟩ := ‹Nonempty Q›
  letI := group h hm a
  obtain ⟨f,g,c,hop⟩ := representation h hm a
  have he : @Equation667 Q ⟨AffineStructure.op f g c⟩ := by
    intro x y
    change x = AffineStructure.op f g c y (AffineStructure.op f g c x
      (AffineStructure.op f g c (AffineStructure.op f g c x x) y))
    simpa only [← hop] using h x y
  exact AffineStructure.affine_prime_square_dvd f g c he hd hr

/-- All orders 3 or 6 modulo nine are excluded for medial E667 magmas. -/
theorem not_medial_of_mod_nine (h : Equation667 Q)
    (hn : Nat.card Q % 9 = 3 ∨ Nat.card Q % 9 = 6) : ¬ Medial (Q := Q) := by
  intro hm
  haveI : Nonempty Q := Finite.card_pos_iff.mp (by omega)
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hh := prime_square_dvd h hm (p := 3)
    (Nat.dvd_of_mod_eq_zero (by omega)) AffineStructure.no_root_three
  have hz := Nat.mod_eq_zero_of_dvd hh
  norm_num at hz
  omega

spectrum_assert representation complete
spectrum_assert prime_square_dvd complete
spectrum_assert not_medial_of_mod_nine complete

end
end Spectrum.E667.MedialAffine
