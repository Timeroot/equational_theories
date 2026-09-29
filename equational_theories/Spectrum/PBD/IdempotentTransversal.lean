import equational_theories.Spectrum.PBD.Closure
import equational_theories.Spectrum.PBD.Transversal

/-! Idempotent orthogonal arrays. Their orders form a PBD-closed set, the
Bose–Shrikhande ingredient in eventual existence of transversal designs. -/
namespace Spectrum.PBD
open Classical PairDecomposition

structure IdempotentTransversal (I Q : Type*) extends Transversal I Q where
  diagonal : ∀ x i, line (x,x) i = x

namespace IdempotentTransversal
variable {I J Q R : Type*}

def reindex (D : IdempotentTransversal I Q) (e : J ≃ I) : IdempotentTransversal J Q :=
  { D.toTransversal.reindex e with diagonal := fun x i => D.diagonal x (e i) }

def restrictIndex (D : IdempotentTransversal I Q) (f : J ↪ I) : IdempotentTransversal J Q :=
  { D.toTransversal.restrictIndex f with diagonal := fun x i => D.diagonal x (f i) }

def relabel (D : IdempotentTransversal I Q) (e : Q ≃ R) : IdempotentTransversal I R := by
  refine { D.toTransversal.relabel e with diagonal := ?_ }
  intro x i
  change e (D.line (e.symm x,e.symm x) i) = x
  rw [D.diagonal,e.apply_symm_apply]

def product (D : IdempotentTransversal I Q) (E : IdempotentTransversal I R) :
    IdempotentTransversal I (Q × R) :=
  { D.toTransversal.product E.toTransversal with
    diagonal := fun x i => Prod.ext (D.diagonal x.1 i) (E.diagonal x.2 i) }

noncomputable def ring [CommRing R] [Finite R] (c : I → R)
    (hu : ∀ i j, i ≠ j → IsUnit (c i - c j)) : IdempotentTransversal I R where
  line p i := p.1 + c i * (p.2-p.1)
  pair i j hij := by
    have hinj : Function.Injective (fun p : R × R =>
        (p.1 + c i * (p.2-p.1),p.1 + c j * (p.2-p.1))) := by
      intro p q h
      have he := Transversal.coord_injective c hu (some i) (some j)
        (fun h => hij (Option.some.inj h))
        (a₁ := (p.1,p.2-p.1)) (a₂ := (q.1,q.2-q.1)) h
      obtain ⟨h1,h2⟩ := Prod.mk.inj he
      exact Prod.ext h1 (by rw [h1] at h2; linear_combination h2)
    exact ⟨hinj,Finite.injective_iff_surjective.mp hinj⟩
  diagonal _ _ := by simp

noncomputable def field {F : Type*} [Field F] [Finite F] (c : I ↪ F) :
    IdempotentTransversal I F :=
  ring c (fun _ _ h => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun he => h (c.injective he))))

section Gluing
variable {K : Set ℕ} {X : Type*} [Finite X] (D : Complete K X)
variable (E : ∀ b : D.blocks, IdempotentTransversal I b.val)

private abbrev tautology : BinaryLaw := ⟨.Leaf false,.Leaf false⟩

private def coordinateModel (i : I) (b : D.blocks) : Model tautology b.val where
  op x y := (E b).line (x,y) i
  idem x := (E b).diagonal x i
  law _ _ := rfl

noncomputable def gluedLine (p : X × X) (i : I) : X :=
  Model.glueOp (fun b : D.blocks => b.val) (coordinateModel D E i) p.1 p.2

omit [Finite X] in
theorem gluedLine_diagonal (x : X) (i : I) : gluedLine D E (x,x) i = x :=
  Model.glueOp_idem _ _ _

omit [Finite X] in
theorem gluedLine_on (b : D.blocks) (x y : b.val) (i : I) :
    gluedLine D E (x.val,y.val) i = ((E b).line (x,y) i).val :=
  Model.glueOp_on _ _ (fun x y h => D.cover x y h trivial) b x y

theorem gluedLine_pair_ne (i j : I) (hij : i ≠ j) {x y : X} (hxy : x ≠ y) :
    gluedLine D E (x,y) i ≠ gluedLine D E (x,y) j := by
  obtain ⟨b,⟨hx,hy⟩,_⟩ := D.cover x y hxy trivial
  let u : b.val := ⟨x,hx⟩
  let v : b.val := ⟨y,hy⟩
  rw [gluedLine_on D E b u v i,gluedLine_on D E b u v j]
  intro he
  have h : (E b).line (u,v) i = (E b).line (u,v) j := Subtype.ext he
  let a := (E b).line (u,v) i
  have hh : (u,v) = (a,a) := (E b).pair i j hij |>.injective
    (Prod.ext ((E b).diagonal a i).symm (h.symm.trans ((E b).diagonal a j).symm))
  exact hxy (congrArg Subtype.val ((congrArg Prod.fst hh).trans (congrArg Prod.snd hh).symm))

noncomputable def glue : IdempotentTransversal I X where
  line := gluedLine D E
  diagonal := gluedLine_diagonal D E
  pair i j hij := by
    have hinj : Function.Injective (fun p : X × X =>
        (gluedLine D E p i,gluedLine D E p j)) := by
      rintro ⟨x,y⟩ ⟨u,v⟩ he
      have hi : gluedLine D E (x,y) i = gluedLine D E (u,v) i := congrArg Prod.fst he
      have hj : gluedLine D E (x,y) j = gluedLine D E (u,v) j := congrArg Prod.snd he
      by_cases hxy : x = y
      · subst y
        have huv : u = v := by
          by_contra h
          exact gluedLine_pair_ne D E i j hij h (by
            rw [← hi,← hj,gluedLine_diagonal,gluedLine_diagonal])
        subst v
        have hxu : x = u := by simpa only [gluedLine_diagonal] using hi
        exact Prod.ext hxu hxu
      · have huv : u ≠ v := by
          intro h
          subst v
          exact gluedLine_pair_ne D E i j hij hxy (by
            rw [hi,hj,gluedLine_diagonal,gluedLine_diagonal])
        obtain ⟨b,⟨hx,hy⟩,_⟩ := D.cover x y hxy trivial
        obtain ⟨c,⟨hu,hv⟩,_⟩ := D.cover u v huv trivial
        let x' : b.val := ⟨x,hx⟩
        let y' : b.val := ⟨y,hy⟩
        let u' : c.val := ⟨u,hu⟩
        let v' : c.val := ⟨v,hv⟩
        have hbi : gluedLine D E (x,y) i ∈ b.val := by
          rw [gluedLine_on D E b x' y' i]; exact ((E b).line (x',y') i).property
        have hbj : gluedLine D E (x,y) j ∈ b.val := by
          rw [gluedLine_on D E b x' y' j]; exact ((E b).line (x',y') j).property
        have hci : gluedLine D E (x,y) i ∈ c.val := by
          rw [hi,gluedLine_on D E c u' v' i]; exact ((E c).line (u',v') i).property
        have hcj : gluedLine D E (x,y) j ∈ c.val := by
          rw [hj,gluedLine_on D E c u' v' j]; exact ((E c).line (u',v') j).property
        have hbc : b = c := (D.cover _ _ (gluedLine_pair_ne D E i j hij hxy) trivial).unique
          ⟨hbi,hbj⟩ ⟨hci,hcj⟩
        subst c
        rw [gluedLine_on D E b x' y' i,gluedLine_on D E b u' v' i] at hi
        rw [gluedLine_on D E b x' y' j,gluedLine_on D E b u' v' j] at hj
        have h := (E b).pair i j hij |>.injective (Prod.ext (Subtype.ext hi) (Subtype.ext hj))
        exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
          (congrArg Subtype.val (congrArg Prod.snd h))
    exact ⟨hinj,Finite.injective_iff_surjective.mp hinj⟩
end Gluing
end IdempotentTransversal

def HasITD (k q : ℕ) : Prop := Nonempty (IdempotentTransversal (Fin k) (Fin q))

namespace HasITD

theorem toHasTD {k q : ℕ} (h : HasITD k q) : HasTD k q :=
  ⟨h.some.toTransversal⟩

theorem one (k : ℕ) : HasITD k 1 := by
  refine ⟨{ line := fun _ _ => 0, pair := ?_, diagonal := ?_ }⟩
  · exact fun _ _ _ => ⟨fun _ _ _ => Subsingleton.elim _ _,
      fun p => ⟨p,Subsingleton.elim _ _⟩⟩
  · exact fun _ _ => Subsingleton.elim _ _

theorem field (F : Type*) [Field F] [Fintype F] {k : ℕ}
    (hk : k ≤ Fintype.card F) : HasITD k (Fintype.card F) := by
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le (α := Fin k) (β := F) (by simpa using hk)
  exact ⟨(IdempotentTransversal.field c).relabel (Fintype.equivFin F)⟩

theorem primePower {p e k : ℕ} (hp : p.Prime) (he : e ≠ 0) (hk : k ≤ p^e) :
    HasITD k (p^e) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p e) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p e) = p^e := by
    rw [← Nat.card_eq_fintype_card,GaloisField.card p e he]
  simpa only [hc] using (field (GaloisField p e) (k := k) (by simpa only [hc] using hk))

theorem mul {k q r : ℕ} (h : HasITD k q) (g : HasITD k r) : HasITD k (q*r) := by
  obtain ⟨D⟩ := h
  obtain ⟨E⟩ := g
  exact ⟨(D.product E).relabel (Fintype.equivFinOfCardEq (by simp))⟩

/-- Bose–Shrikhande: the orders of idempotent arrays are PBD closed. -/
theorem closed (k : ℕ) : DesignClosed {q | HasITD k q} := by
  rintro n ⟨D⟩
  have models (b : D.blocks) : Nonempty (IdempotentTransversal (Fin k) b.val) := by
    obtain ⟨E⟩ := D.sizes _ b.property
    let e : b.val ≃ Fin (Nat.card b.val) := Fintype.equivFinOfCardEq (by simp)
    exact ⟨E.relabel e.symm⟩
  exact ⟨IdempotentTransversal.glue D (fun b => (models b).some)⟩

end HasITD
end Spectrum.PBD
