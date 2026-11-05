import equational_theories.Parastrophes.Equation477Image

/-!
# All cancellation and division in the E477 image basis is controlled by c

For the pair E411 + E4332, put c(x)=x*(x*x). On arbitrary carriers:
* c is injective iff all rows are injective, iff all columns are injective;
* c is surjective iff all rows are surjective, iff all columns are surjective.
Consequently the actual left-division image is precisely this pair together
with bijectivity of c. No finite-cardinality argument is needed.

The fixed points of c form a semisymmetric quasigroup (E14). This submagma
is nonempty whenever the original magma is: x*c(x) is always fixed by c.
These are structural reductions, not an unrestricted single-equation result.
-/
namespace Parastrophes.Eq477Image
open Law

variable {A : Type} (D : Magma A) (h : Basis D)
include h

/-- Crossing converts a column collision directly into a collision of c. -/
theorem columns_injective_of_core (hc : Function.Injective (core D)) (y : A) :
    Function.Injective (fun x => D.op x y) := by
  intro a b hab
  change D.op a y = D.op b y at hab
  apply hc
  rw [← cross D h y a, ← cross D h y b, hab]

/-- A row collision gives a column collision after one crossed application. -/
theorem rows_injective_of_columns
    (hr : ∀ y, Function.Injective (fun x => D.op x y)) (x : A) :
    Function.Injective (D.op x) := by
  intro a b hab
  apply hr (D.op x a)
  calc
    D.op a (D.op x a) = core D x := cross D h a x
    _ = D.op b (D.op x b) := (cross D h b x).symm
    _ = D.op b (D.op x a) := congrArg (D.op b) hab.symm

theorem core_injective_iff_rows :
    Function.Injective (core D) ↔ ∀ x, Function.Injective (D.op x) :=
  ⟨fun hc => rows_injective_of_columns D h (columns_injective_of_core D h hc),
    core_injective_of_rows D h⟩

theorem core_injective_iff_columns :
    Function.Injective (core D) ↔ ∀ y, Function.Injective (fun x => D.op x y) :=
  ⟨columns_injective_of_core D h,
    fun hr => core_injective_of_rows D h (rows_injective_of_columns D h hr)⟩

theorem rows_surjective_of_core (hc : Function.Surjective (core D)) (x : A) :
    Function.Surjective (D.op x) := by
  intro y
  obtain ⟨z, rfl⟩ := hc y
  exact ⟨D.op z x, cross D h x z⟩

theorem columns_surjective_of_core (hc : Function.Surjective (core D)) (y : A) :
    Function.Surjective (fun x => D.op x y) := by
  intro z
  obtain ⟨a, rfl⟩ := hc y
  obtain ⟨b, rfl⟩ := hc z
  exact ⟨D.op a b, rotate D h a b⟩

/-- A preimage of the local right identity in the x-column maps to x under c. -/
theorem core_surjective_of_columns
    (hr : ∀ y, Function.Surjective (fun x => D.op x y)) :
    Function.Surjective (core D) := by
  intro x
  obtain ⟨a, ha⟩ := hr x (D.op x (core D x))
  change D.op a x = D.op x (core D x) at ha
  refine ⟨a, ?_⟩
  rw [← cross D h x a, ha]
  exact diagonal D h x

theorem core_surjective_iff_rows :
    Function.Surjective (core D) ↔ ∀ x, Function.Surjective (D.op x) :=
  ⟨rows_surjective_of_core D h, core_surjective_of_rows D h⟩

theorem core_surjective_iff_columns :
    Function.Surjective (core D) ↔ ∀ y, Function.Surjective (fun x => D.op x y) :=
  ⟨columns_surjective_of_core D h, core_surjective_of_columns D h⟩

omit h in
/-- This strengthens the earlier finite injectivity criterion to an exact
arbitrary-carrier criterion, with bijectivity explicitly retained. -/
theorem inImage_iff_core_bijective :
    InImage Law477 .left D ↔ Basis D ∧ Function.Bijective (core D) := by
  constructor
  · intro hi
    obtain ⟨hb, hq⟩ := (inImage_iff D).mp hi
    exact ⟨hb, core_injective_of_rows D hb (fun x => (hq x).1),
      core_surjective_of_rows D hb (fun x => (hq x).2)⟩
  · rintro ⟨hb, hc⟩
    exact (inImage_iff D).mpr ⟨hb, fun x =>
      ⟨(core_injective_iff_rows D hb).mp hc.1 x, rows_surjective_of_core D hb hc.2 x⟩⟩

/-- The c-fixed submagma is closed because c is an endomorphism. -/
@[implicit_reducible] def fixedMagma : Magma {x : A // core D x = x} :=
  ⟨fun x y => ⟨D.op x.val y.val, by
    rw [core_endomorphism D h, x.property, y.property]⟩⟩

theorem fixed_equation14 : @Equation14 {x : A // core D x = x} (fixedMagma D h) := by
  intro x y
  apply Subtype.ext
  exact ((cross D h y.val x.val).trans x.property).symm

theorem fixed_basis : Basis (fixedMagma D h) := by
  constructor
  · intro x
    exact Subtype.ext (h.1 x.val)
  · intro x y z
    exact Subtype.ext (h.2 x.val y.val z.val)

theorem fixed_core (x : {x : A // core D x = x}) :
    core (fixedMagma D h) x = x := Subtype.ext x.property

/-- The fixed submagma is already a genuine image, with no finiteness
assumption on the containing magma. -/
theorem fixed_inImage : InImage Law477 .left (fixedMagma D h) := by
  apply (inImage_iff_core_bijective (fixedMagma D h)).mpr
  refine ⟨fixed_basis D h, ?_⟩
  have he : core (fixedMagma D h) = id := funext (fixed_core D h)
  rw [he]
  exact Function.bijective_id

theorem fixed_quasigroup : IsQuasigroup (fixedMagma D h) :=
  image_quasigroup (fixedMagma D h) (fixed_inImage D h)

/-- Every nonempty basis model contains this semisymmetric subquasigroup;
no global bijectivity assumption is used to produce an element. -/
theorem fixed_nonempty [Nonempty A] : Nonempty {x : A // core D x = x} := by
  obtain ⟨x⟩ := ‹Nonempty A›
  exact ⟨⟨D.op x (core D x), (local_right_identity D h x).2⟩⟩

omit h in
/-- In an actual division image, the explicit fixed point above is just
the square in the original multiplication. -/
theorem source_square_fixed (M : Magma A) (hd : IsDivision .left M D)
    (hm : @Equation477 A M) (x : A) : core D (M.op x x) = M.op x x := by
  have he := (local_right_identity D (forward M D hd hm) x).2
  rw [core_eq M D hd hm x, hd.2] at he
  exact he

end Parastrophes.Eq477Image
