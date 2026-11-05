import equational_theories.Parastrophes.Equation714ImageCandidate
import equational_theories.Parastrophes.ImageBasis

/-!
# One equation for E714's left-division image on arbitrary carriers

Write H(x,y)=x*(x*(x*y)), F(y,x)=y*H(x,y), and G(z,x)=H(z*x,z).
The identity x=y*F(w,H(G(z,x),y)) forces bijective rows and F(y,x)=x.
Thus it characterizes E464 with left division, without assuming finiteness.

Proof guide:
* The outer y-row is onto. All occurrences of x pass through z*x, so every
  z-row is injective. These observations work on infinite carriers too.
* Varying w and cancelling rows makes F(w,t) independent of w; call it a(t).
  The identity also makes each G(z,-) injective. Since F and G are conjugate
  by a row, a is injective. Further cancellation makes G(z,t) a common b(t).
  The original identity supplies surjectivity, making a and b permutations.
* Put c = b⁻¹ ∘ a⁻¹. Each row conjugates a→c→b→a. Its third power H
  therefore commutes with a. This gives m(a(x),a(y))=m(x,y), from which
  H(a(x),y)=H(x,y). Another calculation gives H(a(x),y)=b(H(x,y)).
  Surjectivity of H forces b=id, and conjugacy then forces a=id.

The expanded equation has 68 operations because G has size 6, H(G(z,x),y)
has size 21, and F repeats that 21-operation argument three times. The
ten-operation basis F(y,x)=x and G(z,x)=x is registered separately below.
No minimality of the single equation is claimed.
-/
namespace Parastrophes.Eq714SingleImage
open Law FreeMagma
open Eq714ImageCandidate (triple F G)

def Compressed {A : Type} (M : Magma A) : Prop :=
  ∀ x y z w, x = M.op y (F M w (triple M (G M z x) y))

theorem leftQuasigroup {A : Type} (M : Magma A) (h : Compressed M) :
    IsSideQuasigroup .left M := by
  intro z
  constructor
  · intro x y he
    have hg : G M z x = G M z y := by simp only [G, he]
    exact (h x z z z).trans ((congrArg (fun t =>
      M.op z (F M z (triple M t z))) hg).trans (h y z z z).symm)
  · intro x
    exact ⟨F M z (triple M (G M z x) z), (h x z z z).symm⟩

theorem of_basis {A : Type} (M : Magma A) (h : @Equation464 A M)
    (hq : IsSideQuasigroup .left M) : Compressed M := by
  have hf (y x) : F M y x = x := (h x y).symm
  have hg (z x) : G M z x = x := by
    apply (hq z).1
    exact hf z (M.op z x)
  intro x y z w
  rw [hg, hf]
  exact h x y

/- The short algebraic core. The two common maps conjugate cyclically under
each row. Cubing a row therefore commutes with them. Applying the same fact
to the row indexed by a(x) forces b=id, and then a=id. -/
private theorem common_maps_trivial {A : Type}
    (m d H : A → A → A) (a b ai bi : A → A)
    (ht : ∀ x y, H x y = m x (m x (m x y)))
    (hf : ∀ x y, m y (H x y) = a x)
    (hg : ∀ x y, H (m y x) y = b x)
    (hc : ∀ x y, m y (a (H (b x) y)) = x)
    (md : ∀ x y, m x (d x y) = y)
    (dm : ∀ x y, d x (m x y) = y)
    (aai : ∀ x, a (ai x) = x) (aia : ∀ x, ai (a x) = x)
    (bbi : ∀ x, b (bi x) = x) (bib : ∀ x, bi (b x) = x) :
    ∀ x, a x = x := by
  let c := fun x => bi (ai x)
  have hd (x y) : H x y = d y (a x) := by
    rw [← hf x y, dm]
  have mb (x y) : m x (b y) = a (m x y) := by
    rw [← hg y x, hf]
  have ma (x y) : m x (a y) = c (m x y) := by
    have he := hc (bi (ai (m x y))) x
    simpa only [bbi, hd, aai, dm, c] using he
  have mbi (x y) : m x (bi y) = ai (m x y) := by
    rw [← bbi y, mb, aia, bib]
  have mai (x y) : m x (ai y) = a (b (m x y)) := by
    have he := ma x (ai y)
    have hh := congrArg (fun t => a (b t)) he
    simpa only [aai, c, bbi] using hh.symm
  have mc (x y) : m x (c y) = b (m x y) := by
    dsimp only [c]
    rw [mbi, mai, aia]
  -- Three row applications traverse the whole cycle a→c→b→a.
  have commute (x y) : H x (a y) = a (H x y) := by
    rw [ht, ma, mc, mb, ← ht]
  have shift (x y) : H (a x) y = b (H x y) := by
    calc
      H (a x) y = H (a (m y (d y x))) y := by rw [md]
      _ = H (m y (b (d y x))) y := by rw [mb]
      _ = b (b (d y x)) := hg _ _
      _ = b (H (m y (d y x)) y) := by rw [hg]
      _ = b (H x y) := by rw [md]
  have invariant (x y) : m (a x) (a y) = m x y := by
    have he := hf (ai (m x y)) (a x)
    rw [commute, hd, aai, dm] at he
    exact he
  have row_shift (x y) : m (a x) y = a (b (m x y)) := by
    calc
      m (a x) y = m (a x) (a (ai y)) := by rw [aai]
      _ = m x (ai y) := invariant _ _
      _ = a (b (m x y)) := mai _ _
  have cube_shift (x y) : H (a x) y = H x y := by
    rw [ht, ht]
    simp only [row_shift, ma, mb, c, bbi, aai, aia]
  -- Compare the two formulas for the row cube indexed by a(x).
  have bid (x) : b x = x := by
    let y := d x (d x (d x x))
    have hy : H x y = x := by simp only [ht, y, md]
    rw [← hy, ← shift, cube_shift]
  intro x
  calc
    a x = a (m x (d x x)) := by rw [md]
    _ = m x (b (d x x)) := (mb _ _).symm
    _ = x := by rw [bid, md]

private theorem equation464_of_nonempty {A : Type} [Nonempty A]
    (M : Magma A) (h : Compressed M) : @Equation464 A M := by
  classical
  let o : A := Classical.choice inferInstance
  have hq := leftQuasigroup M h
  let le (x : A) := Equiv.ofBijective (M.op x) (hq x)
  let d (x y : A) := (le x).symm y
  have md (x y) : M.op x (d x y) = y := (le x).apply_symm_apply y
  have dm (x y) : d x (M.op x y) = y := (le x).symm_apply_apply y
  have ht (x : A) : Function.Bijective (triple M x) :=
    (hq x).comp ((hq x).comp (hq x))
  let a := F M o
  -- The argument H(G(o,o),y) ranges over the whole carrier as y varies.
  -- Thus the apparently local cancellation really proves independence for
  -- every input t, not merely for some distinguished subalgebra.
  have hf (w t) : F M w t = a t := by
    obtain ⟨y, hy⟩ := (ht (G M o o)).2 t
    have he := (h o y o w).symm.trans (h o y o o)
    have he' := (hq y).1 he
    simpa only [hy] using he'
  have hgi (z : A) : Function.Injective (G M z) := by
    intro x y he
    exact (h x o z o).trans ((congrArg (fun t =>
      M.op o (F M o (triple M t o))) he).trans (h y o z o).symm)
  have conjugate (x y) : a (M.op x y) = M.op x (G M x y) := by
    rw [← hf x]
    rfl
  have hai : Function.Injective a := by
    intro x y he
    apply (le o).symm.injective
    change d o x = d o y
    apply hgi o
    apply (hq o).1
    rw [← conjugate, ← conjugate, md, md]
    exact he
  have hcol (y : A) : Function.Injective (fun x => triple M x y) := by
    intro x z he
    apply hai
    rw [← hf y x, ← hf y z]
    exact congrArg (M.op y) he
  let b := G M o
  have hg (z x) : G M z x = b x := by
    have he := (h x o z o).symm.trans (h x o o o)
    exact hcol o (hai ((hq o).1 he))
  have has : Function.Surjective a := by
    intro t
    refine ⟨triple M (G M o (M.op o t)) o, ?_⟩
    exact (hq o).1 (h (M.op o t) o o o).symm
  have hbs : Function.Surjective b := by
    intro t
    obtain ⟨x, hx⟩ := has (M.op o t)
    refine ⟨d o x, (hq o).1 ?_⟩
    simpa only [← conjugate, md, b] using hx
  let ae := Equiv.ofBijective a ⟨hai, has⟩
  let be := Equiv.ofBijective b ⟨hgi o, hbs⟩
  have ha := common_maps_trivial M.op d (triple M) a b ae.symm be.symm
    (fun _ _ => rfl) (fun x y => hf y x)
    (fun x y => hg y x)
    (fun x y => by simpa only [← hg o x] using (h x y o o).symm)
    md dm ae.apply_symm_apply ae.symm_apply_apply
    be.apply_symm_apply be.symm_apply_apply
  intro x y
  exact ((hf y x).trans (ha x)).symm

theorem equation464 {A : Type} (M : Magma A) (h : Compressed M) :
    @Equation464 A M := by
  intro x y
  letI : Nonempty A := ⟨x⟩
  exact equation464_of_nonempty M h x y

theorem characterizes {A : Type} (M : Magma A) :
    Compressed M ↔ InImage Law714 .left M := by
  constructor
  · intro h
    classical
    have hq := leftQuasigroup M h
    let le (x : A) := Equiv.ofBijective (M.op x) (hq x)
    let D : Magma A := ⟨fun x y => (le x).symm y⟩
    have hd : IsDivision .left M D :=
      ⟨fun x y => (le x).apply_symm_apply y, fun x y => (le x).symm_apply_apply y⟩
    have hD : @satisfies _ A D Law714 :=
      (Catalogue.left_characterizes464_all_rotated A D trivial).mpr
        ⟨M, (@Law464.models_iff A M).mpr (equation464 M h), hd⟩
    exact ⟨D, hD, division_symm hd⟩
  · intro h
    apply of_basis M (Eq714ImageCandidate.image_equation464 M h)
    obtain ⟨D, _, hd⟩ := h
    exact sideQuasigroup_of_division (division_symm hd)

/-- A 68-operation identity, with four variables. -/
def compressedLaw : NatMagmaLaw :=
  let H (x y : FreeMagma Nat) := x ⋆ (x ⋆ (x ⋆ y))
  let F (y x : FreeMagma Nat) := y ⋆ H x y
  let G (z x : FreeMagma Nat) := H (z ⋆ x) z
  ⟨Lf 0, Lf 1 ⋆ F (Lf 3) (H (G (Lf 2) (Lf 0)) (Lf 1))⟩

theorem compressedLaw_iff {A : Type} (M : Magma A) :
    @satisfies _ A M compressedLaw ↔ Compressed M := by
  constructor
  · intro h x y z w
    exact h (fun n => if n = 0 then x else if n = 1 then y else if n = 2 then z else w)
  · intro h v
    exact h (v 0) (v 1) (v 2) (v 3)

@[parastrophe_result] theorem left_characterizes714_all_single :
    Characterizes .all Law714 .left compressedLaw := by
  intro A M _
  exact (compressedLaw_iff M).trans (characterizes M)

/-- The second half of the shorter exact basis: G(z,x)=x. -/
def reverseLaw : NatMagmaLaw :=
  let u := Lf 1 ⋆ Lf 0
  ⟨Lf 0, u ⋆ (u ⋆ (u ⋆ Lf 1))⟩

private theorem reverseLaw_iff {A : Type} (M : Magma A) :
    @satisfies _ A M reverseLaw ↔ ∀ z x, G M z x = x := by
  constructor
  · intro h z x
    exact (h (fun n => if n = 0 then x else z)).symm
  · intro h v
    exact (h (v 1) (v 0)).symm

/-- Keep the ten-operation, two-equation basis alongside the longer single
equation. Its two halves express both directions of each row inverse. -/
@[parastrophe_basis] theorem left714_all_basis :
    CharacterizesBasis .all Law714 .left [Law464, reverseLaw] := by
  intro A M _
  simp [Law464.models_iff, reverseLaw_iff]
  constructor
  · rintro ⟨hf, hg⟩
    have hq : IsSideQuasigroup .left M := by
      intro y
      constructor
      · intro x z he
        have he' : G M y x = G M y z := by simp only [G, he]
        simpa only [hg] using he'
      · intro x
        exact ⟨triple M x y, (hf x y).symm⟩
    exact (characterizes M).mp (of_basis M hf hq)
  · intro h
    have hf := Eq714ImageCandidate.image_equation464 M h
    obtain ⟨D, _, hd⟩ := h
    have hq := sideQuasigroup_of_division (division_symm hd)
    refine ⟨hf, fun z x => (hq z).1 ?_⟩
    exact (hf (M.op z x) z).symm

end Parastrophes.Eq714SingleImage
