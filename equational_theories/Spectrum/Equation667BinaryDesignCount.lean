import equational_theories.Spectrum.Equation667BinaryDesignClassification

/-! Including the arbitrary origin in every binary fiber gives exactly
2^(n+4b) labelled extensions of a finite five-point design algebra. -/
namespace Spectrum.E667.BinaryDesign
open Classical
variable {Q I : Type*} (B : I → Set Q) (e : ∀ i, B i ≃ ZMod 5)
    (cover : ∀ x y : Q, x ≠ y → ∃! i, x ∈ B i ∧ y ∈ B i)
include cover

abbrev Cocycles := {C : Q → Q → ZMod 2 // BinaryExtensions.Cocycle (base B e) C}

private theorem base_law : @Equation667 Q ⟨base B e⟩ :=
  ((BinaryExtensions.law_iff (base B e) _).mp (law B e (fun _ _ => 0) cover)).1

private theorem gauge_cocycle (C : Q → Q → ZMod 2)
    (hc : BinaryExtensions.Cocycle (base B e) C) (h : Q → ZMod 2) :
    BinaryExtensions.Cocycle (base B e) (BinaryExtensions.gauge (base B e) C h) :=
  ((BinaryExtensions.law_iff (base B e) _).mp
    (BinaryExtensions.gauge_law (base B e) C h
      ((BinaryExtensions.law_iff (base B e) C).mpr ⟨base_law B e cover,hc⟩))).2

omit cover in
private theorem gauge_twice (C : Q → Q → ZMod 2) (h : Q → ZMod 2) :
    BinaryExtensions.gauge (base B e) (BinaryExtensions.gauge (base B e) C h) h = C := by
  funext x y
  simp only [BinaryExtensions.gauge]
  ring_nf
  reduce_mod_char

omit cover in
private theorem gauge_diag (C : Q → Q → ZMod 2) (h : Q → ZMod 2) (x : Q) :
    BinaryExtensions.gauge (base B e) C h x x = C x x+h x := by
  simp only [BinaryExtensions.gauge, base_idem]
  ring_nf
  reduce_mod_char

noncomputable def normalizationEquiv : Cocycles B e ≃ (Q → ZMod 2) × NormalizedCocycles B e where
  toFun C := (fun x => C.val x x,
    ⟨BinaryExtensions.gauge (base B e) C.val (fun x => C.val x x),
      BinaryExtensions.normalize_diag (base B e) (base_idem B e) C.val,
      gauge_cocycle B e cover C.val C.property _⟩)
  invFun D := ⟨BinaryExtensions.gauge (base B e) D.2.val D.1,
    gauge_cocycle B e cover D.2.val D.2.property.2 D.1⟩
  left_inv C := Subtype.ext (gauge_twice B e C.val _)
  right_inv D := by
    apply Prod.ext
    · funext x
      exact (gauge_diag B e D.2.val D.1 x).trans (by rw [D.2.property.1,zero_add])
    · apply Subtype.ext
      have hd : (fun x => BinaryExtensions.gauge (base B e) D.2.val D.1 x x) = D.1 := by
        funext x
        rw [gauge_diag, D.2.property.1, zero_add]
      change BinaryExtensions.gauge (base B e)
        (BinaryExtensions.gauge (base B e) D.2.val D.1) _ = D.2.val
      rw [hd, gauge_twice]

/-- Exact count before choosing the zero of each fiber. Each point contributes
one origin bit and each five-element block contributes four cocycle bits. -/
theorem all_count [Finite Q] [Finite I] :
    Nat.card (Cocycles B e) = 2 ^ (Nat.card Q + 4 * Nat.card I) := by
  haveI : Finite (NormalizedCocycles B e) := Finite.of_equiv _ (dataEquiv B e cover)
  rw [Nat.card_congr (normalizationEquiv B e cover), Nat.card_prod,
    normalized_count B e cover]
  letI := Fintype.ofFinite Q
  have hf : Nat.card (Q → ZMod 2) = 2 ^ Nat.card Q := by
    simp [Nat.card_eq_fintype_card]
  rw [hf, pow_add]

abbrev Extensions := {g : Q → Q → ZMod 2 → ZMod 2 → ZMod 2 //
  @Equation667 (Q × ZMod 2) ⟨BinaryExtensions.generalOp (base B e) g⟩}

/-- The cocycle count includes every possible multiplication table on the
binary fibers, not only operations initially presented in affine form. -/
noncomputable def allExtensionEquiv [Finite Q] : Extensions B e ≃ Cocycles B e where
  toFun g := ⟨fun i j => g.val i j 0 0, by
    have he := BinaryExtensions.every_fiber_extension (base B e) g.val g.property
    have hh := g.property
    rw [he] at hh
    exact ((BinaryExtensions.law_iff (base B e) _).mp hh).2⟩
  invFun C := ⟨fun i j a b => a+b+C.val i j,
    (BinaryExtensions.law_iff (base B e) C.val).mpr ⟨base_law B e cover,C.property⟩⟩
  left_inv g := by
    apply Subtype.ext
    funext i j a b
    have he := BinaryExtensions.every_fiber_extension (base B e) g.val g.property
    have hh := congrArg Prod.snd (congrFun (congrFun he (i,a)) (j,b))
    exact hh.symm
  right_inv C := by
    apply Subtype.ext
    funext i j
    exact zero_add _

theorem all_extension_count [Finite Q] [Finite I] :
    Nat.card (Extensions B e) = 2 ^ (Nat.card Q + 4 * Nat.card I) := by
  rw [Nat.card_congr (allExtensionEquiv B e cover)]
  exact all_count B e cover

/-- The commutative cocycles are exactly changes of origin in the trivial
extension. Their diagonal entries determine the entire multiplication. -/
theorem symmetric_iff (C : Cocycles B e) :
    (∀ x y, C.val x y = C.val y x) ↔
      C.val = BinaryExtensions.gauge (base B e) (fun _ _ => 0) (fun x => C.val x x) := by
  constructor
  · intro hs
    let D := normalizationEquiv B e cover C
    obtain ⟨v,hv,he⟩ := complete B e cover D.2.val D.2.property.1 D.2.property.2
    have hd (x y : Q) : D.2.val x y = D.2.val y x := by
      change BinaryExtensions.gauge (base B e) C.val (fun t => C.val t t) x y =
        BinaryExtensions.gauge (base B e) C.val (fun t => C.val t t) y x
      simp only [BinaryExtensions.gauge, hs x y, base_commutative B e cover x y]
      ring
    have hc : ∀ i, BinaryFive.Constant (v i) := by
      apply (commutative_iff B e v cover).mp
      intro x y
      apply Prod.ext
      · exact base_commutative B e cover x.1 y.1
      · change x.2+y.2+coefficient B e v x.1 y.1 =
          y.2+x.2+coefficient B e v y.1 x.1
        rw [← he, hd x.1 y.1]
        ring
    have hz : D.2.val = fun _ _ => 0 := by
      rw [he]
      funext x y
      exact coefficient_zero_of_constant B e v hc x y
    have hh := congrArg (fun F => BinaryExtensions.gauge (base B e) F (fun x => C.val x x)) hz
    change BinaryExtensions.gauge (base B e)
      (BinaryExtensions.gauge (base B e) C.val (fun x => C.val x x)) _ = _ at hh
    simpa only [gauge_twice] using hh
  · intro he x y
    rw [he]
    simp only [BinaryExtensions.gauge, base_commutative B e cover x y]
    ring

abbrev CommutativeCocycles := {C : Cocycles B e // ∀ x y, C.val x y = C.val y x}

/-- Every commutative binary extension is isomorphic over the quotient to
the direct product of the base algebra and the two-element group. -/
theorem commutative_isomorphism (C : CommutativeCocycles B e) :
    ∃ E : (Q × ZMod 2) ≃ (Q × ZMod 2),
      (∀ x, (E x).1 = x.1) ∧
      ∀ x y, E (BinaryExtensions.op (base B e) C.val.val x y) =
        BinaryExtensions.op (base B e) (fun _ _ => 0) (E x) (E y) := by
  let h := fun x => C.val.val x x
  refine ⟨BinaryExtensions.shiftEquiv h, fun _ => rfl, ?_⟩
  intro x y
  change BinaryExtensions.shift h (BinaryExtensions.op (base B e) C.val.val x y) = _
  rw [BinaryExtensions.shift_hom]
  have hh := (symmetric_iff B e cover C.val).mp C.property
  have hz : BinaryExtensions.gauge (base B e) C.val.val h = (fun _ _ => 0) := by
    change C.val.val = BinaryExtensions.gauge (base B e) (fun _ _ => 0) h at hh
    rw [hh, gauge_twice]
  rw [hz]
  rfl

/-- Arbitrary fiber origins are the only freedom in a commutative extension. -/
noncomputable def commutativeEquiv : CommutativeCocycles B e ≃ (Q → ZMod 2) where
  toFun C x := C.val.val x x
  invFun h := ⟨⟨BinaryExtensions.gauge (base B e) (fun _ _ => 0) h,
    gauge_cocycle B e cover _ (by intro x y; simp) h⟩, by
      intro x y
      simp only [BinaryExtensions.gauge, base_commutative B e cover x y]
      ring⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((symmetric_iff B e cover C.val).mp C.property).symm
  right_inv h := by
    funext x
    exact (gauge_diag B e (fun _ _ => 0) h x).trans (zero_add _)

/-- Among 2^(n+4b) labelled binary extensions, exactly 2^n are commutative. -/
theorem commutative_count [Finite Q] :
    Nat.card (CommutativeCocycles B e) = 2 ^ Nat.card Q := by
  rw [Nat.card_congr (commutativeEquiv B e cover)]
  letI := Fintype.ofFinite Q
  simp [Nat.card_eq_fintype_card]

spectrum_assert symmetric_iff complete
spectrum_assert commutative_isomorphism complete
spectrum_assert commutative_count complete
spectrum_assert all_extension_count complete
spectrum_assert normalizationEquiv complete
spectrum_assert all_count complete
end Spectrum.E667.BinaryDesign
