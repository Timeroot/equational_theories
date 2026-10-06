import equational_theories.Spectrum.Equation667BinaryFiveProperties
import equational_theories.Spectrum.Equation667BinaryExtensions

/-! Independent binary data on the blocks of a five-point design give E667
magmas on twice the point set. Blocks overlap in whole two-element fibers;
no idempotency assumption is imposed on the resulting magma. -/
namespace Spectrum.E667.BinaryDesign
open Classical
variable {Q I : Type*} (B : I → Set Q) (e : ∀ i, B i ≃ ZMod 5)
    (v : I → ZMod 5 → ZMod 2)
variable (cover : ∀ x y : Q, x ≠ y → ∃! i, x ∈ B i ∧ y ∈ B i)

noncomputable def base (x y : Q) : Q :=
  if h : ∃ i, x ∈ B i ∧ y ∈ B i then
    (e h.choose |>.symm <| BinaryFive.base (e h.choose ⟨x,h.choose_spec.1⟩)
      (e h.choose ⟨y,h.choose_spec.2⟩)).val
  else x

noncomputable def coefficient (x y : Q) : ZMod 2 :=
  if h : ∃ i, x ∈ B i ∧ y ∈ B i then
    BinaryFive.cocycle (v h.choose) (e h.choose ⟨x,h.choose_spec.1⟩)
      (e h.choose ⟨y,h.choose_spec.2⟩)
  else 0

theorem base_idem (x : Q) : base B e x x = x := by
  unfold base
  split
  · simp only [BinaryFive.base_idem, Equiv.symm_apply_apply]
  · rfl

theorem coefficient_diag (x : Q) : coefficient B e v x x = 0 := by
  unfold coefficient
  split
  · exact BinaryFive.cocycle_diag _ _
  · rfl

include cover in
theorem base_on (i : I) (x y : B i) :
    base B e x.val y.val = (e i |>.symm <| BinaryFive.base (e i x) (e i y)).val := by
  have he : ∃ j, x.val ∈ B j ∧ y.val ∈ B j := ⟨i,x.property,y.property⟩
  by_cases hxy : x.val = y.val
  · have heq : x = y := Subtype.ext hxy
    subst y
    simp only [base_idem, BinaryFive.base_idem, Equiv.symm_apply_apply]
  · have hi : he.choose = i := (cover x.val y.val hxy).unique he.choose_spec
      ⟨x.property,y.property⟩
    simp only [base, dif_pos he]
    have transfer (j : I) (hj : j = i) (hx : x.val ∈ B j) (hy : y.val ∈ B j) :
        (e j |>.symm <| BinaryFive.base (e j ⟨x.val,hx⟩) (e j ⟨y.val,hy⟩)).val =
          (e i |>.symm <| BinaryFive.base (e i x) (e i y)).val := by
      subst j
      rfl
    exact transfer _ hi _ _

include cover in
theorem coefficient_on (i : I) (x y : B i) :
    coefficient B e v x.val y.val = BinaryFive.cocycle (v i) (e i x) (e i y) := by
  have he : ∃ j, x.val ∈ B j ∧ y.val ∈ B j := ⟨i,x.property,y.property⟩
  by_cases hxy : x.val = y.val
  · have heq : x = y := Subtype.ext hxy
    subst y
    rw [coefficient_diag, BinaryFive.cocycle_diag]
  · have hi : he.choose = i := (cover x.val y.val hxy).unique he.choose_spec
      ⟨x.property,y.property⟩
    simp only [coefficient, dif_pos he]
    have transfer (j : I) (hj : j = i) (hx : x.val ∈ B j) (hy : y.val ∈ B j) :
        BinaryFive.cocycle (v j) (e j ⟨x.val,hx⟩) (e j ⟨y.val,hy⟩) =
          BinaryFive.cocycle (v i) (e i x) (e i y) := by
      subst j
      rfl
    exact transfer _ hi _ _

def point (i : I) (a : ZMod 5) : Q := (e i |>.symm <| a).val

include cover in
theorem base_map (i : I) (a b : ZMod 5) :
    base B e (point B e i a) (point B e i b) = point B e i (BinaryFive.base a b) := by
  simpa only [point, Equiv.apply_symm_apply] using base_on B e cover i ((e i).symm a) ((e i).symm b)

include cover in
theorem coefficient_map (i : I) (a b : ZMod 5) :
    coefficient B e v (point B e i a) (point B e i b) = BinaryFive.cocycle (v i) a b := by
  simpa only [point, Equiv.apply_symm_apply] using coefficient_on B e v cover i ((e i).symm a) ((e i).symm b)

noncomputable def op : (Q × ZMod 2) → (Q × ZMod 2) → (Q × ZMod 2) :=
  BinaryExtensions.op (base B e) (coefficient B e v)

include cover in
/-- Arbitrary and independent binary functions on the blocks preserve E667. -/
theorem law : @Equation667 (Q × ZMod 2) ⟨op B e v⟩ := by
  apply (BinaryExtensions.law_iff (base B e) (coefficient B e v)).mpr
  constructor
  · intro x y
    change x = base B e y (base B e x (base B e (base B e x x) y))
    by_cases hxy : x = y
    · subst y
      simp only [base_idem]
    · obtain ⟨i, hi, _⟩ := cover x y hxy
      let a := e i ⟨x, hi.1⟩
      let b := e i ⟨y, hi.2⟩
      have ha : point B e i a = x := by simp only [point, a, Equiv.symm_apply_apply]
      have hb : point B e i b = y := by simp only [point, b, Equiv.symm_apply_apply]
      rw [← ha, ← hb]
      simp only [base_map B e cover, BinaryFive.base_idem, BinaryFive.base_law]
  · intro x y
    by_cases hxy : x = y
    · subst y
      simp only [base_idem, coefficient_diag, add_zero]
    · obtain ⟨i, hi, _⟩ := cover x y hxy
      let a := e i ⟨x, hi.1⟩
      let b := e i ⟨y, hi.2⟩
      have ha : point B e i a = x := by simp only [point, a, Equiv.symm_apply_apply]
      have hb : point B e i b = y := by simp only [point, b, Equiv.symm_apply_apply]
      rw [← ha, ← hb]
      simp only [base_map B e cover, coefficient_map B e v cover, BinaryFive.base_idem,
        BinaryFive.cocycle_diag, zero_add, BinaryFive.cocycle_law]

theorem square (x : Q × ZMod 2) : op B e v x x = (x.1, 0) :=
  BinaryExtensions.square (base B e) (base_idem B e) (coefficient B e v) (coefficient_diag B e v) x

def lift (i : I) (x : ZMod 5 × ZMod 2) : Q × ZMod 2 := (point B e i x.1, x.2)

theorem lift_injective (i : I) : Function.Injective (lift B e i) := by
  intro x y hh
  apply Prod.ext
  · apply (e i).symm.injective
    apply Subtype.ext
    exact congrArg Prod.fst hh
  · exact congrArg (fun z : Q × ZMod 2 => z.2) hh

include cover in
theorem lift_hom (i : I) (x y : ZMod 5 × ZMod 2) :
    lift B e i (BinaryFive.op (v i) x y) = op B e v (lift B e i x) (lift B e i y) := by
  apply Prod.ext
  · exact (base_map B e cover i x.1 y.1).symm
  · change x.2 + y.2 + BinaryFive.cocycle (v i) x.1 y.1 =
      x.2 + y.2 + coefficient B e v (point B e i x.1) (point B e i y.1)
    rw [coefficient_map B e v cover]

include cover in
/-- A nonconstant choice on even one block forces global noncommutativity. -/
theorem noncommutative_of_block (i : I) (hi : ¬ BinaryFive.Constant (v i)) :
    ¬ ∀ x y, op B e v x y = op B e v y x := by
  intro hc
  apply hi
  apply (BinaryFive.commutative_iff_constant (v i)).mp
  intro x y
  apply lift_injective B e i
  rw [lift_hom B e v cover, lift_hom B e v cover]
  exact hc _ _

include cover in
/-- A nonconstant block also obstructs global mediality. -/
theorem nonmedial_of_block (i : I) (hi : ¬ BinaryFive.Constant (v i)) :
    ¬ ∀ x y z w, op B e v (op B e v x y) (op B e v z w) =
      op B e v (op B e v x z) (op B e v y w) := by
  intro hm
  apply hi
  apply (BinaryFive.medial_iff_constant (v i)).mp
  intro x y z w
  apply lift_injective B e i
  simpa only [lift_hom B e v cover] using hm (lift B e i x) (lift B e i y) (lift B e i z) (lift B e i w)

/-- Exactly one point in each binary fiber is idempotent. -/
theorem idempotent_iff (x : Q × ZMod 2) : op B e v x x = x ↔ x.2 = 0 := by
  rw [square]
  constructor
  · intro hh; exact (congrArg Prod.snd hh).symm
  · intro hh; exact Prod.ext rfl hh.symm

theorem idempotents_card : Nat.card {x : Q × ZMod 2 // op B e v x x = x} = Nat.card Q := by
  apply Nat.card_congr
  exact {
    toFun := fun x => x.val.1
    invFun := fun i => ⟨(i,0),square B e v _⟩
    left_inv := fun x => Subtype.ext (Prod.ext rfl ((idempotent_iff B e v x.val).mp x.property).symm)
    right_inv := fun _ => rfl }

include cover in
theorem base_commutative (x y : Q) : base B e x y = base B e y x := by
  by_cases hxy : x = y
  · subst y; rfl
  obtain ⟨i,hi,_⟩ := cover x y hxy
  rw [base_on B e cover i ⟨x,hi.1⟩ ⟨y,hi.2⟩,
    base_on B e cover i ⟨y,hi.2⟩ ⟨x,hi.1⟩]
  congr 2
  exact congrArg (fun z : ZMod 5 => 3*z) (add_comm _ _)

theorem coefficient_zero_of_constant (hv : ∀ i, BinaryFive.Constant (v i)) (x y : Q) :
    coefficient B e v x y = 0 := by
  unfold coefficient
  split
  · exact (BinaryFive.cocycle_zero_iff _).mpr (hv _) _ _
  · rfl

include cover in
/-- Global commutativity leaves no normalized binary freedom on any block. -/
theorem commutative_iff : (∀ x y, op B e v x y = op B e v y x) ↔
    ∀ i, BinaryFive.Constant (v i) := by
  constructor
  · intro hc i
    by_contra hh
    exact noncommutative_of_block B e v cover i hh hc
  · intro hv x y
    apply Prod.ext
    · exact base_commutative B e cover x.1 y.1
    · change x.2+y.2+coefficient B e v x.1 y.1 = y.2+x.2+coefficient B e v y.1 x.1
      rw [coefficient_zero_of_constant B e v hv, coefficient_zero_of_constant B e v hv]
      abel

include cover in
/-- Squaring is a homomorphism exactly when every normalized block is trivial. -/
theorem square_hom_iff :
    (∀ x y, op B e v (op B e v x y) (op B e v x y) =
      op B e v (op B e v x x) (op B e v y y)) ↔
    ∀ i, BinaryFive.Constant (v i) := by
  constructor
  · intro hs i
    apply (BinaryFive.cocycle_zero_iff (v i)).mp
    intro a b
    have hh := congrArg Prod.snd (hs (point B e i a,0) (point B e i b,0))
    simp only [square] at hh
    change (0 : ZMod 2) = 0+0+coefficient B e v (point B e i a) (point B e i b) at hh
    simpa only [zero_add, coefficient_map B e v cover] using hh.symm
  · intro hv x y
    rw [square, square, square]
    apply Prod.ext
    · rfl
    · change (0 : ZMod 2) = 0+0+coefficient B e v x.1 y.1
      rw [coefficient_zero_of_constant B e v hv]
      rfl

include cover in
/-- Mediality requires both a medial base and trivial normalized block data. -/
theorem medial_iff :
    (∀ x y z w, op B e v (op B e v x y) (op B e v z w) =
      op B e v (op B e v x z) (op B e v y w)) ↔
    (∀ i, BinaryFive.Constant (v i)) ∧
      ∀ x y z w, base B e (base B e x y) (base B e z w) =
        base B e (base B e x z) (base B e y w) := by
  constructor
  · intro hm
    refine ⟨(square_hom_iff B e v cover).mp (fun x y => hm x y x y), ?_⟩
    intro x y z w
    exact congrArg Prod.fst (hm (x,0) (y,0) (z,0) (w,0))
  · rintro ⟨hv,hb⟩ x y z w
    apply Prod.ext
    · exact hb x.1 y.1 z.1 w.1
    · simp only [op, BinaryExtensions.op, coefficient_zero_of_constant B e v hv,
        add_zero]
      ring

spectrum_assert square_hom_iff complete
spectrum_assert medial_iff complete
spectrum_assert idempotents_card complete
spectrum_assert commutative_iff complete
spectrum_assert law complete
spectrum_assert noncommutative_of_block complete
spectrum_assert nonmedial_of_block complete
end Spectrum.E667.BinaryDesign
