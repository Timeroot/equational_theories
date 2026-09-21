import equational_theories.Definability.Basic
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Prod

/-! Compactness bounds finite model counts for unrestricted FO recovery.
A pair of defining formulas has a first-order witness sentence. If every
source model has a reversible interpretation, compactness gives finitely many
such pairs covering all nonempty source models. Each pair can recover at most
one source table from each target table, giving a uniform counting bound. -/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw
namespace FORecoveryCompactness

abbrev GraphFormula := MagmaLanguage.Formula (Option (Fin 2))

def Represents {G : Type} (M N : Magma G) (q : GraphFormula) : Prop :=
  ∀ v, @Formula.Realize _ G M.FOStructure _ q v ↔ v ∈ N.Graph

noncomputable def close {α : Type} [Finite α] (q : MagmaLanguage.Formula α) :
    MagmaLanguage.Sentence := (q.relabel Sum.inr).iAlls α

theorem realize_close {G α : Type} [Finite α] (M : Magma G) (q : MagmaLanguage.Formula α) :
    @Sentence.Realize _ G M.FOStructure (close q) ↔
      ∀ v, @Formula.Realize _ G M.FOStructure _ q v := by
  simp only [close, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
    Sum.elim_comp_inr]

noncomputable def functional (q : GraphFormula) : MagmaLanguage.Sentence :=
  close ((q.relabel (fun a => a.elim (Sum.inr ()) Sum.inl)).iExsUnique Unit)

theorem realize_functional {G : Type} (M : Magma G) (q : GraphFormula) :
    @Sentence.Realize _ G M.FOStructure (functional q) ↔
      ∀ v : Fin 2 → G, ∃! w : Unit → G,
        @Formula.Realize _ G M.FOStructure _ q (fun (a : Option (Fin 2)) => a.elim (w ()) v) := by
  rw [functional, realize_close]
  simp only [Formula.realize_iExsUnique, Formula.realize_relabel]
  have hm (v : Fin 2 → G) (w : Unit → G) :
      Sum.elim v w ∘ (fun (a : Option (Fin 2)) => a.elim (Sum.inr ()) Sum.inl) =
        (fun (a : Option (Fin 2)) => a.elim (w ()) v) := by
    funext a; cases a <;> rfl
  simp only [hm]

theorem functional_of_represents {G : Type} (M N : Magma G) (q : GraphFormula)
    (h : Represents M N q) : @Sentence.Realize _ G M.FOStructure (functional q) := by
  rw [realize_functional]
  intro v
  refine ⟨fun _ => N.op (v 0) (v 1), ?_, ?_⟩
  · exact (h _).mpr rfl
  · intro w hw
    funext i
    exact ((h _).mp hw).symm

theorem represents_of_functional {G : Type} (M : Magma G) (q : GraphFormula)
    (h : @Sentence.Realize _ G M.FOStructure (functional q)) : ∃ N, Represents M N q := by
  classical
  rw [realize_functional] at h
  let N : Magma G := ⟨fun x y => ((h ![x,y]).choose) ()⟩
  refine ⟨N, ?_⟩
  intro v
  have hv : ![v (some 0), v (some 1)] = fun i => v (some i) := by
    funext i; fin_cases i <;> rfl
  have hw := (h ![v (some 0), v (some 1)]).choose_spec
  constructor
  · intro hh
    have he : (fun _ : Unit => v none) = (h ![v (some 0), v (some 1)]).choose := by
      apply hw.2
      convert hh using 1
      funext a
      cases a with
      | none => rfl
      | some i => exact congrFun hv i
    exact (congrFun he ()).symm
  · intro hh
    convert hw.1 using 1
    funext a
    cases a with
    | none => exact hh.symm
    | some i => exact (congrFun hv i).symm

def functionDefinitions (q : GraphFormula) {n : ℕ} (g : MagmaLanguage.Functions n) :
    MagmaLanguage.Formula (Option (Fin n)) :=
  @MagmaLanguage.onFunctions (fun n => MagmaLanguage.Formula (Option (Fin n))) q n g

def relationDefinitions {n : ℕ} (r : MagmaLanguage.Relations n) : MagmaLanguage.Formula (Fin n) :=
  isEmptyElim (show Empty from r)

def translate {α : Type} (q : GraphFormula) (f : MagmaLanguage.Formula α) :
    MagmaLanguage.Formula α :=
  f.subst_definitions (functionDefinitions q) relationDefinitions

theorem realize_translate {G α : Type} (M N : Magma G) (q : GraphFormula)
    (h : Represents M N q) (f : MagmaLanguage.Formula α) (v : α → G) :
    @Formula.Realize _ G M.FOStructure _ (translate q f) v ↔
      @Formula.Realize _ G N.FOStructure _ f v := by
  have hf : ∀ {n} (g : MagmaLanguage.Functions n),
      (@Formula.Realize _ G M.FOStructure _ (functionDefinitions q g) : Set (_ → G)) =
      Function.tupleGraph (fun v => @Term.realize _ G N.FOStructure _ v g.term) := by
    intro n g
    have hn : n = 2 := by
      by_contra hn
      exact isEmptyElim (show Empty from by simpa [MagmaLanguage, hn] using g)
    subst n
    ext w
    simpa only [functionDefinitions, MagmaLanguage.onFunctions, ↓reduceDIte, Term.realize_function_term] using h w
  have he := @Formula.subst_definitions_eq MagmaLanguage MagmaLanguage α G
    N.FOStructure M.FOStructure (functionDefinitions q) relationDefinitions
    f hf (fun r => isEmptyElim (show Empty from r))
  exact Iff.of_eq (congrFun he v)

def graphFormula : GraphFormula :=
  Term.equal (Functions.apply₂ () (.var (some 0)) (.var (some 1))) (.var none)

theorem realize_graph {G : Type} (M : Magma G) (v : Option (Fin 2) → G) :
    @Formula.Realize _ G M.FOStructure _ graphFormula v ↔ v ∈ M.Graph := Iff.rfl

theorem realize_toTerm {G α : Type} (M : Magma G) (t : FreeMagma α) (v : α → G) :
    @Term.realize _ G M.FOStructure _ v t.toTerm = @FreeMagma.evalInMagma α G M v t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change M.op (@Term.realize _ G M.FOStructure _ v a.toTerm)
      (@Term.realize _ G M.FOStructure _ v b.toTerm) = _
    rw [ha, hb]
    rfl

noncomputable def lawSentence (L : NatMagmaLaw) : MagmaLanguage.Sentence :=
  close (Term.equal L.toFin.lhs.toTerm L.toFin.rhs.toTerm)

theorem realize_lawSentence {G : Type} (M : Magma G) (L : NatMagmaLaw) :
    @Sentence.Realize _ G M.FOStructure (lawSentence L) ↔ @satisfies _ G M L := by
  rw [lawSentence, realize_close, ← @Law.satisfies_toFin _ G _ M L]
  simp only [Formula.realize_equal, realize_toTerm]
  rfl

noncomputable def witness (L : NatMagmaLaw) (q r : GraphFormula) : MagmaLanguage.Sentence :=
  functional q ⊓ (translate q (lawSentence L) ⊓ close ((translate q r).iff graphFormula))

theorem realize_witness {G : Type} (M : Magma G) (L : NatMagmaLaw) (q r : GraphFormula) :
    @Sentence.Realize _ G M.FOStructure (witness L q r) ↔
      ∃ N : Magma G, @satisfies _ G N L ∧ Represents M N q ∧ Represents N M r := by
  letI : MagmaLanguage.Structure G := M.FOStructure
  simp only [witness, Sentence.Realize, Formula.realize_inf]
  constructor
  · rintro ⟨hq, hL, hr⟩
    obtain ⟨N, hN⟩ := represents_of_functional M q hq
    refine ⟨N, ?_, hN, ?_⟩
    · exact (realize_lawSentence N L).mp ((realize_translate M N q hN _ _).mp hL)
    · intro v
      have hh := (realize_close M _).mp hr v
      rw [Formula.realize_iff, realize_translate M N q hN, realize_graph] at hh
      exact hh
  · rintro ⟨N, hL, hq, hr⟩
    refine ⟨functional_of_represents M N q hq, ?_, ?_⟩
    · exact (realize_translate M N q hq _ _).mpr ((realize_lawSentence N L).mpr hL)
    · apply (realize_close M _).mpr
      intro v
      rw [Formula.realize_iff, realize_translate M N q hq, realize_graph]
      exact hr v


@[implicit_reducible] def asMagma {G : Type} (S : MagmaLanguage.Structure G) : Magma G :=
  ⟨fun x y => @Structure.funMap MagmaLanguage G S 2 () ![x,y]⟩

theorem structure_asMagma {G : Type} (S : MagmaLanguage.Structure G) :
    (asMagma S).FOStructure = S := by
  cases S with
  | mk f r =>
    unfold asMagma Magma.FOStructure
    congr 1
    · funext n t v
      have hn : n = 2 := by
        by_contra hn
        exact isEmptyElim (show Empty from by simpa [MagmaLanguage, hn] using t)
      subst n
      have ht : t = () := Subsingleton.elim _ _
      subst t
      change @f 2 () ![v 0, v 1] = @f 2 () v
      congr 1
      funext i
      fin_cases i <;> rfl
    · funext n t
      exact isEmptyElim (show Empty from t)

theorem exists_witness {G : Type} (M : Magma G) (L : NatMagmaLaw)
    (h : L.StructuralOnMagma M) : ∃ q r : GraphFormula,
      @Sentence.Realize _ G M.FOStructure (witness L q r) := by
  obtain ⟨N, hL, hq, hr⟩ := h
  rw [@Set.empty_definable_iff G MagmaLanguage M.FOStructure] at hq
  rw [@Set.empty_definable_iff G MagmaLanguage N.FOStructure] at hr
  obtain ⟨q, hq⟩ := hq
  obtain ⟨r, hr⟩ := hr
  refine ⟨q, r, (realize_witness M L q r).mpr ⟨N, hL, ?_, ?_⟩⟩
  · intro v
    exact Iff.of_eq (congrArg (fun s => v ∈ s) hq.symm)
  · intro v
    exact Iff.of_eq (congrArg (fun s => v ∈ s) hr.symm)

theorem finite_cover (A B : NatMagmaLaw) (h : B.StructuralFrom A) :
    ∃ s : Finset (GraphFormula × GraphFormula),
      ∀ {G : Type} [Nonempty G] (M : Magma G), @satisfies _ G M A →
        ∃ qr ∈ s, @Sentence.Realize _ G M.FOStructure (witness B qr.1 qr.2) := by
  classical
  let W : GraphFormula × GraphFormula → MagmaLanguage.Sentence := fun qr => witness B qr.1 qr.2
  let T : MagmaLanguage.Theory := {lawSentence A} ∪ Set.range (fun qr => (W qr).not)
  have hbad : T ⊨ᵇ (⊥ : MagmaLanguage.Sentence) := by
    apply Theory.models_sentence_iff.mpr
    intro X
    let M : Magma X := asMagma X.struc
    have hA : @satisfies _ X M A := by
      apply (realize_lawSentence M A).mp
      have hh := Theory.realize_sentence_of_mem T (Set.mem_union_left _ (Set.mem_singleton _))
        (M := X)
      change @Sentence.Realize _ X (asMagma X.struc).FOStructure (lawSentence A)
      rw [structure_asMagma]
      exact hh
    obtain ⟨q, r, hqr⟩ := exists_witness M B (h M hA)
    have hn := Theory.realize_sentence_of_mem T
      (Set.mem_union_right _ (Set.mem_range_self (q,r))) (M := X)
    have hn' : ¬ @Sentence.Realize _ X M.FOStructure (W (q,r)) := by
      change ¬ @Sentence.Realize _ X (asMagma X.struc).FOStructure (W (q,r))
      rw [structure_asMagma]
      exact (Sentence.realize_not X).mp hn
    exact (hn' hqr).elim
  obtain ⟨T0, hsub, hT0⟩ := Theory.models_iff_finset_models.mp hbad
  let index (φ : MagmaLanguage.Sentence) : GraphFormula × GraphFormula :=
    if hh : φ ∈ Set.range (fun qr => (W qr).not) then hh.choose else (⊥, ⊥)
  have hindex (φ : MagmaLanguage.Sentence) (hh : φ ∈ Set.range (fun qr => (W qr).not)) :
      (W (index φ)).not = φ := by
    simp only [index, dif_pos hh]
    exact hh.choose_spec
  refine ⟨T0.image index, ?_⟩
  intro G _ M hM
  by_contra hn
  push Not at hn
  letI : MagmaLanguage.Structure G := M.FOStructure
  haveI : G ⊨ (T0 : MagmaLanguage.Theory) := by
    constructor
    intro φ hφ
    rcases hsub hφ with hφA | hφW
    · have he : φ = lawSentence A := Set.mem_singleton_iff.mp hφA
      rw [he]
      exact (realize_lawSentence M A).mpr hM
    · rw [← hindex φ hφW]
      apply (Sentence.realize_not G).mpr
      exact hn (index φ) (Finset.mem_image.mpr ⟨φ, hφ, rfl⟩)
  have hh := hT0.realize_sentence G
  exact hh


theorem represents_unique {G : Type} (N M M' : Magma G) (q : GraphFormula)
    (h : Represents N M q) (h' : Represents N M' q) : M = M' := by
  cases M with
  | mk f =>
    cases M' with
    | mk g =>
      congr 1
      funext x y
      exact ((h' (fun a => a.elim (f x y) ![x,y])).mp
        ((h (fun a => a.elim (f x y) ![x,y])).mpr rfl)).symm

abbrev Tables (A : NatMagmaLaw) (G : Type) := {f : G → G → G // @satisfies _ G ⟨f⟩ A}

theorem bounded_counts (A B : NatMagmaLaw) (h : B.StructuralFrom A) :
    ∃ K : ℕ, ∀ (G : Type) [Fintype G] [Nonempty G],
      Nat.card (Tables A G) ≤ K * Nat.card (Tables B G) := by
  classical
  obtain ⟨s, hs⟩ := finite_cover A B h
  refine ⟨s.card, ?_⟩
  intro G _ _
  have hc (f : Tables A G) : ∃ p : s × Tables B G,
      Represents (⟨p.2.val⟩ : Magma G) ⟨f.val⟩ p.1.val.2 := by
    obtain ⟨qr, hqr, hw⟩ := hs (⟨f.val⟩ : Magma G) f.property
    obtain ⟨N, hN, _, hback⟩ := (realize_witness (⟨f.val⟩ : Magma G) B qr.1 qr.2).mp hw
    exact ⟨(⟨qr,hqr⟩, ⟨N.op,hN⟩), hback⟩
  choose p hp using hc
  have hi : Function.Injective p := by
    intro f g he
    have hg := hp g
    rw [← he] at hg
    have heq := represents_unique _ _ _ _ (hp f) hg
    apply Subtype.ext
    exact congrArg (fun t : Magma G => @Magma.op G t) heq
  have hle := Nat.card_le_card_of_injective p hi
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe] using hle

theorem not_structural_of_unbounded_counts (A B : NatMagmaLaw)
    (hc : ∀ K : ℕ, ∃ n : ℕ, 0 < n ∧ K * Nat.card (Tables B (Fin n)) <
      Nat.card (Tables A (Fin n))) : ¬ B.StructuralFrom A := by
  intro h
  obtain ⟨K, hK⟩ := bounded_counts A B h
  obtain ⟨n, hn, hcount⟩ := hc K
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact (not_lt_of_ge (hK (Fin n))) hcount

end FORecoveryCompactness

/-- info: 'FORecoveryCompactness.bounded_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORecoveryCompactness.bounded_counts
