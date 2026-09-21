import equational_theories.Definability.Invariant

/-! Reversible term interpretations pass to surjective homomorphic images.
The same two terms define the image companion and recover the image operation;
surjectivity transfers the target equation. -/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma
namespace TermRecoveryHom

variable {G H α : Type} (M : Magma G) (N : Magma H)

@[reducible] def termMagma (t : MagmaLanguage.Term (Fin 2)) : Magma G where
  op x y := @Language.Term.realize _ _ M.FOStructure _ ![x, y] t

theorem termMagma_definable (t : MagmaLanguage.Term (Fin 2)) :
    @Set.TermDefinable G ∅ MagmaLanguage M.FOStructure (Fin 2) (termMagma M t).FinArityOp := by
  letI := M.FOStructure
  rw [Set.termDefinable_empty_iff]
  refine ⟨t, ?_⟩
  funext v
  change @Language.Term.realize _ _ M.FOStructure _ ![v 0, v 1] t =
    @Language.Term.realize _ _ M.FOStructure _ v t
  congr 1
  funext i
  fin_cases i <;> rfl

theorem exists_termMagma (M' : Magma G)
    (h : @Set.TermDefinable G ∅ MagmaLanguage M.FOStructure (Fin 2) M'.FinArityOp) :
    ∃ t, M' = termMagma M t := by
  letI := M.FOStructure
  rw [Set.termDefinable_empty_iff] at h
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  cases M'
  congr 1
  funext x y
  exact congrFun ht ![x,y]

theorem realize_map (f : G → H) (hf : ∀ x y, f (M.op x y) = N.op (f x) (f y))
    (t : MagmaLanguage.Term α) (v : α → G) :
    f (@Language.Term.realize _ _ M.FOStructure _ v t) =
      @Language.Term.realize _ _ N.FOStructure _ (f ∘ v) t := by
  induction t with
  | var => rfl
  | func F ts ih =>
    obtain rfl := MagmaLanguage.arity_eq_two F
    simp only [Language.Term.realize, Magma.FOStructure_funMap, Magma.FinArityOp]
    rw [hf, ih 0, ih 1]

theorem termMagma_map (f : G → H) (hf : ∀ x y, f (M.op x y) = N.op (f x) (f y))
    (t : MagmaLanguage.Term (Fin 2)) (x y : G) :
    f ((termMagma M t).op x y) = (termMagma N t).op (f x) (f y) := by
  change f (@Language.Term.realize _ _ M.FOStructure _ ![x,y] t) = _
  rw [realize_map M N f hf]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem law_map (f : G → H) (hf : ∀ x y, f (M.op x y) = N.op (f x) (f y))
    (hs : Function.Surjective f) (L : MagmaLaw α) (hL : @satisfies _ G M L) :
    @satisfies _ H N L := by
  classical
  intro v
  let w : α → G := fun a => (hs (v a)).choose
  have hw : f ∘ w = v := funext fun a => (hs (v a)).choose_spec
  let fh : @MagmaHom G H M N := ⟨f, hf⟩
  have h1 := @FreeMagma.evalInMagma_hom α G H M N w fh L.lhs
  have h2 := @FreeMagma.evalInMagma_hom α G H M N w fh L.rhs
  change @FreeMagma.evalInMagma α H N v L.lhs = @FreeMagma.evalInMagma α H N v L.rhs
  rw [← hw]
  exact h1.symm.trans ((congrArg f (hL w)).trans h2)

theorem transfer_companion (f : G → H) (hf : ∀ x y, f (M.op x y) = N.op (f x) (f y))
    (hs : Function.Surjective f) (L : MagmaLaw α) (M' : Magma G)
    (hL : @satisfies _ G M' L)
    (hfwd : @Set.TermDefinable G ∅ MagmaLanguage M.FOStructure (Fin 2) M'.FinArityOp)
    (hback : @Set.TermDefinable G ∅ MagmaLanguage M'.FOStructure (Fin 2) M.FinArityOp) :
    ∃ N' : Magma H, @satisfies _ H N' L ∧
      @Set.TermDefinable H ∅ MagmaLanguage N.FOStructure (Fin 2) N'.FinArityOp ∧
      @Set.TermDefinable H ∅ MagmaLanguage N'.FOStructure (Fin 2) N.FinArityOp ∧
      ∀ x y, f (M'.op x y) = N'.op (f x) (f y) := by
  obtain ⟨t, rfl⟩ := exists_termMagma M M' hfwd
  obtain ⟨s, he⟩ := exists_termMagma (termMagma M t) M hback
  have hft := termMagma_map M N f hf t
  have hfs := termMagma_map (termMagma M t) (termMagma N t) f hft s
  have hn : N = termMagma (termMagma N t) s := by
    cases N with
    | mk op =>
      congr 1
      funext x y
      obtain ⟨a, rfl⟩ := hs x
      obtain ⟨b, rfl⟩ := hs y
      calc
        op (f a) (f b) = f (M.op a b) := (hf a b).symm
        _ = f ((termMagma (termMagma M t) s).op a b) := by rw [← he]
        _ = (termMagma (termMagma ⟨op⟩ t) s).op (f a) (f b) := hfs a b
  refine ⟨termMagma N t, law_map _ _ f hft hs L hL, termMagma_definable N t, ?_, hft⟩
  rw [show N.FinArityOp = (termMagma (termMagma N t) s).FinArityOp from
    congrArg Magma.FinArityOp hn]
  exact termMagma_definable (termMagma N t) s

theorem transfer (f : G → H) (hf : ∀ x y, f (M.op x y) = N.op (f x) (f y))
    (hs : Function.Surjective f) (L : MagmaLaw α) (h : L.TermStructuralOnMagma M) :
    L.TermStructuralOnMagma N := by
  obtain ⟨M', hL, hfwd, hback⟩ := h
  obtain ⟨N', hN, hfwd', hback', _⟩ := transfer_companion M N f hf hs L M' hL hfwd hback
  exact ⟨N', hN, hfwd', hback'⟩

end TermRecoveryHom
