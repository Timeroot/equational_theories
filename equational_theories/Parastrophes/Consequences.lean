import equational_theories.Parastrophes.Uniform
import equational_theories.Definability.FiniteFlavour
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Consequences of an exact division correspondence

An exact image alone only describes source models which possess the division.
The source-side bijectivity hypothesis below is essential: it makes the
correspondence total on both model classes. These are conversions of kinds of
evidence, not transitive closure of the relation graph.
-/
namespace Parastrophes
open Law FreeMagma FirstOrder.Language

private theorem realize_term {G α : Type} (M : Magma G) (t : FreeMagma α) (v : α → G) :
    @Term.realize _ G M.FOStructure _ v t.toTerm = @evalInMagma _ G M v t := by
  induction t with
  | Leaf a => rfl
  | Fork a b ha hb =>
    simp only [FreeMagma.toTerm, Term.realize_functions_apply₂, Magma.FOStructure_funMap]
    exact congrArg₂ M.op ha hb

theorem uniformTermWitness_recovery {scope L side t}
    (h : UniformTermWitness scope L side t) : TermRecovery scope L side :=
  uniform_implies_term ⟨t, h⟩

/-- Division is FO-definable by one atomic equation, on any carrier. -/
theorem division_definable {G : Type} {side : Side} {M D : Magma G}
    (h : IsDivision side M D) :
    @Set.Definable _ ∅ MagmaLanguage M.FOStructure _ D.Graph := by
  letI := M.FOStructure
  cases side with
  | left =>
    refine ⟨Term.equal (Functions.apply₂ (Sum.inl ()) (Term.var (some 0)) (Term.var none))
      (Term.var (some 1)), ?_⟩
    ext v
    change D.op (v (some 0)) (v (some 1)) = v none ↔ M.op (v (some 0)) (v none) = v (some 1)
    exact ⟨fun he => he ▸ h.1 _ _, fun he => (congrArg (D.op (v (some 0))) he).symm.trans (h.2 _ _)⟩
  | right =>
    refine ⟨Term.equal (Functions.apply₂ (Sum.inl ()) (Term.var none) (Term.var (some 1)))
      (Term.var (some 0)), ?_⟩
    ext v
    change D.op (v (some 0)) (v (some 1)) = v none ↔ M.op (v none) (v (some 1)) = v (some 0)
    exact ⟨fun he => he ▸ h.1 _ _, fun he =>
      (congrArg (fun z => D.op z (v (some 1))) he).symm.trans (h.2 _ _)⟩

/-- Even without source-side bijectivity, every target is structurally a source. -/
theorem characterizes_structural_backward_all {L K side}
    (h : Characterizes .all L side K) : L.StructuralFrom K := by
  intro G D hD
  obtain ⟨M, hm, hd⟩ := (h G D trivial).mp hD
  exact ⟨M, hm, division_definable (division_symm hd), division_definable hd⟩

theorem characterizes_structural_backward_fin {L K side}
    (h : Characterizes .fin L side K) : L.StructuralFromFin K := by
  intro G _ D hD
  obtain ⟨M, hm, hd⟩ := (h G D (inferInstance : Finite G)).mp hD
  exact ⟨M, hm, division_definable (division_symm hd), division_definable hd⟩

theorem termMagma_termDefinable {G : Type} (M : Magma G) (t : FreeMagma (Fin 2)) :
    @Set.TermDefinable _ ∅ MagmaLanguage M.FOStructure _ (termMagma M t).FinArityOp := by
  letI := M.FOStructure
  refine ⟨(MagmaLanguage.lhomWithConstants (∅ : Set G)).onTerm t.toTerm, ?_⟩
  funext v
  rw [LHom.realize_onTerm, realize_term]
  change @evalInMagma _ _ M (fun i => if i = 0 then v 0 else v 1) t = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Per-model terms suffice; there is no requirement for a uniform term. -/
theorem characterizes_termStructuralOnMagma {scope L K side}
    (h : Characterizes scope L side K)
    (hl : TermRecovery scope L side) (hk : TermRecovery scope K side)
    {G : Type} (M : Magma G) (hG : scope.Allows G) (hM : @satisfies _ G M L) :
    K.TermStructuralOnMagma M := by
  obtain ⟨t, ht⟩ := hl G M hG hM
  have hK := (h G (termMagma M t) hG).mpr ⟨M, hM, ht⟩
  obtain ⟨u, hu⟩ := hk G (termMagma M t) hG hK
  refine ⟨termMagma M t, hK, termMagma_termDefinable M t, ?_⟩
  have he := division_unique hu (division_symm ht)
  simpa only [he] using termMagma_termDefinable (termMagma M t) u

theorem characterizes_termStructural_all {L K side}
    (h : Characterizes .all L side K) (hl : TermRecovery .all L side) :
    K.TermStructuralFrom L := by
  have hk := uniform_implies_term (sideQuasigroup_uniform_all (characterizes_sideQuasigroup h))
  intro G M hM
  exact characterizes_termStructuralOnMagma h hl hk M trivial hM

theorem characterizes_termStructural_fin {L K side}
    (h : Characterizes .fin L side K) (hl : TermRecovery .fin L side) :
    K.TermStructuralFromFin L := by
  have hk := sideQuasigroup_term_fin (characterizes_sideQuasigroup h)
  intro G _ M hM
  exact characterizes_termStructuralOnMagma h hl hk M (inferInstance : Finite G) hM

/-- Operations on one fixed, labelled carrier. -/
def Models (G : Type) (L : NatMagmaLaw) := {M : Magma G // @satisfies _ G M L}

instance Models.finite {G : Type} [Finite G] (L : NatMagmaLaw) : Finite (Models G L) := by
  apply Finite.of_injective (fun M : Models G L => M.val.op)
  intro ⟨⟨m⟩, hm⟩ ⟨⟨n⟩, hn⟩ he
  cases he
  rfl

/-- Division gives an actual bijection of model sets, not just equal nonemptiness. -/
noncomputable def characterizes_modelEquiv {scope L K side}
    (h : Characterizes scope L side K) (hs : SideQuasigroupLaw scope L side)
    (G : Type) (hG : scope.Allows G) : Models G L ≃ Models G K := by
  classical
  have hf (M : Models G L) : ∃ D : Models G K, IsDivision side M.val D.val := by
    obtain ⟨D, hd, hi⟩ := (characterizes_symm h hs G M.val hG).mp M.property
    exact ⟨⟨D, hd⟩, division_symm hi⟩
  have hb (D : Models G K) : ∃ M : Models G L, IsDivision side M.val D.val := by
    obtain ⟨M, hm, hi⟩ := (h G D.val hG).mp D.property
    exact ⟨⟨M, hm⟩, hi⟩
  exact {
    toFun := fun M => (hf M).choose
    invFun := fun D => (hb D).choose
    left_inv := fun M => Subtype.ext (division_unique
      (division_symm (hb (hf M).choose).choose_spec)
      (division_symm (hf M).choose_spec))
    right_inv := fun D => Subtype.ext (division_unique
      (hf (hb D).choose).choose_spec (hb D).choose_spec)
  }

theorem characterizes_modelEquiv_division {scope L K side}
    (h : Characterizes scope L side K) (hs : SideQuasigroupLaw scope L side)
    (G : Type) (hG : scope.Allows G) (M : Models G L) :
    IsDivision side M.val (characterizes_modelEquiv h hs G hG M).val := by
  exact (Classical.choose_spec (show ∃ D : Models G K, IsDivision side M.val D.val from by
    obtain ⟨D, hd, hi⟩ := (characterizes_symm h hs G M.val hG).mp M.property
    exact ⟨⟨D, hd⟩, division_symm hi⟩))

/-- Same model counts on every allowed carrier. An explicit model bijection is
retained in `characterizes_modelEquiv`, including on infinite carriers. -/
def SameLabelledSpectrum (scope : Scope) (L K : NatMagmaLaw) : Prop :=
  ∀ G : Type, scope.Allows G → Nonempty (Models G L ≃ Models G K)

theorem characterizes_sameLabelledSpectrum {scope L K side}
    (h : Characterizes scope L side K) (hs : SideQuasigroupLaw scope L side) :
    SameLabelledSpectrum scope L K :=
  fun G hG => ⟨characterizes_modelEquiv h hs G hG⟩

theorem SameLabelledSpectrum.counts {L K} (h : SameLabelledSpectrum .fin L K) (n : Nat) :
    Nat.card (Models (Fin n) L) = Nat.card (Models (Fin n) K) :=
  Nat.card_congr (h (Fin n) (inferInstance : Finite (Fin n))).some

/-- Isomorphism of operations, with the carrier labels allowed to change. -/
def Models.Isomorphic {G : Type} {L : NatMagmaLaw} (M N : Models G L) : Prop :=
  ∃ e : G ≃ G, ∀ x y, e (M.val.op x y) = N.val.op (e x) (e y)

/-- Models up to isomorphism on a fixed carrier. -/
def UnlabelledModels (G : Type) (L : NatMagmaLaw) := Quot (@Models.Isomorphic G L)

/-- Any relabelling preserves multiplication exactly when it preserves division. -/
theorem division_preserves_isomorphism {G : Type} {side : Side} {M N D E : Magma G}
    (hd : IsDivision side M D) (he : IsDivision side N E) (e : G ≃ G)
    (hm : ∀ x y, e (M.op x y) = N.op (e x) (e y)) :
    ∀ x y, e (D.op x y) = E.op (e x) (e y) := by
  have hn := sideQuasigroup_of_division he
  intro x y
  cases side with
  | left =>
    apply (hn (e x)).1
    rw [← hm, hd.1, he.1]
  | right =>
    apply (hn (e y)).1
    change N.op (e (D.op x y)) (e y) = N.op (E.op (e x) (e y)) (e y)
    rw [← hm, hd.1, he.1]

noncomputable def characterizes_unlabelledEquiv {scope L K side}
    (h : Characterizes scope L side K) (hs : SideQuasigroupLaw scope L side)
    (G : Type) (hG : scope.Allows G) : UnlabelledModels G L ≃ UnlabelledModels G K := by
  apply Quot.congr (characterizes_modelEquiv h hs G hG)
  intro M N
  have hm := characterizes_modelEquiv_division h hs G hG M
  have hn := characterizes_modelEquiv_division h hs G hG N
  constructor <;> rintro ⟨e, he⟩
  · exact ⟨e, division_preserves_isomorphism hm hn e he⟩
  · exact ⟨e, division_preserves_isomorphism (division_symm hm) (division_symm hn) e he⟩

/-- Equality of both labelled and unlabelled fine spectra. We retain bijections,
which also make sense for infinite carriers, rather than only natural-number counts. -/
def SameFineSpectrum (scope : Scope) (L K : NatMagmaLaw) : Prop :=
  SameLabelledSpectrum scope L K ∧
    ∀ G : Type, scope.Allows G → Nonempty (UnlabelledModels G L ≃ UnlabelledModels G K)

theorem characterizes_sameFineSpectrum {scope L K side}
    (h : Characterizes scope L side K) (hs : SideQuasigroupLaw scope L side) :
    SameFineSpectrum scope L K :=
  ⟨characterizes_sameLabelledSpectrum h hs,
    fun G hG => ⟨characterizes_unlabelledEquiv h hs G hG⟩⟩

theorem SameFineSpectrum.counts {L K} (h : SameFineSpectrum .fin L K) (n : Nat) :
    Nat.card (Models (Fin n) L) = Nat.card (Models (Fin n) K) ∧
    Nat.card (UnlabelledModels (Fin n) L) = Nat.card (UnlabelledModels (Fin n) K) :=
  ⟨h.1.counts n, Nat.card_congr (h.2 (Fin n) (inferInstance : Finite (Fin n))).some⟩

end Parastrophes
