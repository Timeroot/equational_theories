import equational_theories.Parastrophes.TriangleCompletion
import equational_theories.Parastrophes.Catalogue
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic.Group
import Mathlib.Data.Countable.Defs

/-! Both division images of E1719 fail closure under taking submagmas.
A countable partition into group triangles controls the second iterate of its
turn at every word in a chosen subset. In division, word length then increases.
-/
namespace Parastrophes.Eq1719ImageObstruction
open FreeGroup Law FreeMagma
noncomputable section

abbrev Carrier := FreeGroup Nat

instance : Countable Carrier := FreeGroup.toWord_injective.countable

/-- The first generator, together with words starting negatively and ending
positively. The two fresh partners inserted by the completion never lie here. -/
def bounded (x : Carrier) : Prop :=
  x = FreeGroup.of 0 ∨
    (∃ i, x.toWord.head? = some (i, false)) ∧
    (∃ j, x.toWord.getLast? = some (j, true))

/-- Arguments entering right division from the second protected subset. -/
def rightInput (x : Carrier) : Prop :=
  x.toWord.head? = some (0,true) ∧
    ∃ k : Nat, 0 < k ∧ x.toWord.getLast? = some (k,false)

def allowed (x z : Carrier) : Prop :=
  bounded x ∨ rightInput x → ∃ k : Nat, 0 < k ∧ z = (FreeGroup.of k)⁻¹

private theorem fresh_letters (F : Finset Carrier) (a : Carrier) :
    ∃ k : Nat, 0 < k ∧ ∀ x ∈ insert a F, ∀ e ∈ x.toWord, e.1 ≠ k := by
  classical
  let used : Finset Nat := (insert a F).biUnion (fun x => (x.toWord.map Prod.fst).toFinset)
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset (insert 0 used)
  have hk0 : k ≠ 0 := fun h => hk (h ▸ Finset.mem_insert_self 0 used)
  refine ⟨k, Nat.pos_of_ne_zero hk0, ?_⟩
  intro x hx e he hek
  apply hk
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, ?_⟩
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨e, he, hek⟩

private theorem fresh_inverse {a : Carrier} {k : Nat}
    (ha : ∀ e ∈ a.toWord, e.1 ≠ k) :
    ∀ e ∈ a⁻¹.toWord, e.1 ≠ k := by
  intro e he
  rw [FreeGroup.toWord_inv] at he
  simp only [FreeGroup.invRev, List.mem_map, List.mem_reverse] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact ha f hf

private theorem fresh_word {a : Carrier} {k : Nat}
    (ha : ∀ e ∈ a.toWord, e.1 ≠ k) :
    (FreeGroup.of k * a⁻¹).toWord = (k, true) :: a⁻¹.toWord := by
  have hr : FreeGroup.IsReduced ((k,true) :: a⁻¹.toWord) := by
    have hi := fresh_inverse ha
    cases h : a⁻¹.toWord with
    | nil => exact FreeGroup.IsReduced.singleton
    | cons e es =>
      apply FreeGroup.isReduced_cons_cons.mpr
      refine ⟨?_, ?_⟩
      · intro he
        exact False.elim (hi e (by simp [h]) he.symm)
      · rw [← h]
        exact FreeGroup.isReduced_toWord
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_of]
  exact hr.reduce_eq

private theorem fresh_partners (F : Finset Carrier) (a : Carrier) (_ha : a ∉ F) :
    ∃ b c, b ∉ F ∧ c ∉ F ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a*c*b = 1 ∧
      allowed a c ∧ allowed b a ∧ allowed c b := by
  classical
  obtain ⟨k, hk, hf⟩ := fresh_letters F a
  have hfa := hf a (Finset.mem_insert_self ..)
  let b : Carrier := FreeGroup.of k * a⁻¹
  let c : Carrier := (FreeGroup.of k)⁻¹
  have hbword : b.toWord = (k,true) :: a⁻¹.toWord := fresh_word hfa
  have hcword : c.toWord = [(k,false)] := by simp [c, FreeGroup.toWord_inv, FreeGroup.invRev]
  have hbne (x : Carrier) (hx : x ∈ insert a F) : x ≠ b := by
    intro he
    have hm : (k,true) ∈ x.toWord := by rw [he, hbword]; simp
    exact hf x hx _ hm rfl
  have hcne (x : Carrier) (hx : x ∈ insert a F) : x ≠ c := by
    intro he
    have hm : (k,false) ∈ x.toWord := by rw [he, hcword]; simp
    exact hf x hx _ hm rfl
  have hbc : b ≠ c := by
    intro he
    have := congrArg (fun x : Carrier => x.toWord.head?) he
    simp [hbword, hcword] at this
  have hnb : ¬ bounded b := by
    rintro (he | ⟨⟨i, hi⟩, _⟩)
    · have := congrArg (fun x : Carrier => x.toWord.head?) he
      simp [hbword, FreeGroup.toWord_of] at this
      omega
    · simp [hbword] at hi
  have hnbR : ¬ rightInput b := by
    intro h
    have := h.1
    simp [hbword] at this
    omega
  have hncR : ¬ rightInput c := by
    intro h
    have := h.1
    simp [hcword] at this
  have hnc : ¬ bounded c := by
    rintro (he | ⟨_, ⟨j, hj⟩⟩)
    · have := congrArg (fun x : Carrier => x.toWord.head?) he
      simp [hcword, FreeGroup.toWord_of] at this
    · simp [hcword] at hj
  refine ⟨b,c,?_,?_,hbne a (Finset.mem_insert_self ..),
    hcne a (Finset.mem_insert_self ..),hbc,?_,?_,?_,?_⟩
  · intro h; exact hbne b (Finset.mem_insert_of_mem h) rfl
  · intro h; exact hcne c (Finset.mem_insert_of_mem h) rfl
  · dsimp [b,c]; group
  · intro _; exact ⟨k,hk,rfl⟩
  · exact fun h => h.elim (fun h => False.elim (hnb h)) (fun h => False.elim (hnbR h))
  · exact fun h => h.elim (fun h => False.elim (hnc h)) (fun h => False.elim (hncR h))

private theorem completion : ∃ s : Carrier → Carrier,
    (∀ x, s (s (s x)) = x) ∧
    (∀ x, x * s (s x) * s x = 1) ∧ ∀ x, allowed x (s (s x)) :=
  TriangleCompletion.complete allowed fresh_partners
section Construction
variable (s : Carrier → Carrier) (hcube : ∀ x, s (s (s x)) = x)
    (htriangle : ∀ x, x * s (s x) * s x = 1)
    (hcontrol : ∀ x, allowed x (s (s x)))

@[implicit_reducible] def source : Magma Carrier :=
  ⟨fun x y => (s (s x))⁻¹ * y⁻¹⟩
@[implicit_reducible] def division : Magma Carrier :=
  ⟨fun x y => y⁻¹ * (s (s x))⁻¹⟩

include htriangle in
theorem source_square (x : Carrier) : (source s).op x x = s x := by
  change (s (s x))⁻¹ * x⁻¹ = s x
  calc
    _ = ((s (s x))⁻¹ * x⁻¹) * (x * s (s x) * s x) := by rw [htriangle]; group
    _ = s x := by group

include hcube htriangle in
theorem source_law : @Equation1719 Carrier (source s) := by
  intro x y
  rw [source_square s htriangle, source_square s htriangle]
  change x = (s (s (s y)))⁻¹ * ((s (s (s x)))⁻¹ * y⁻¹)⁻¹
  rw [hcube, hcube]
  group

theorem isDivision : IsDivision .left (source s) (division s) := by
  constructor <;> intro x y
  · change (s (s x))⁻¹ * (y⁻¹ * (s (s x))⁻¹)⁻¹ = y
    group
  · change ((s (s x))⁻¹ * y⁻¹)⁻¹ * (s (s x))⁻¹ = y
    group

private theorem inverse_ends {y : Carrier} (hy : bounded y) :
    (∃ j, y⁻¹.toWord.head? = some (j,false)) ∧
    (y⁻¹.toWord.getLast? = some (0,false) ∨
      ∃ i, y⁻¹.toWord.getLast? = some (i,true)) := by
  rcases hy with rfl | ⟨⟨i,hi⟩,⟨j,hj⟩⟩
  · simp [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.invRev]
  · constructor
    · exact ⟨j, by simp [FreeGroup.toWord_inv, FreeGroup.invRev, List.head?_reverse, hj]⟩
    · exact Or.inr ⟨i, by simp [FreeGroup.toWord_inv, FreeGroup.invRev, List.getLast?_reverse, hi]⟩

include hcontrol in
theorem division_word {x y : Carrier} (hx : bounded x) (hy : bounded y) :
    ∃ k : Nat, 0 < k ∧
      ((division s).op x y).toWord = y⁻¹.toWord ++ [(k,true)] := by
  obtain ⟨k,hk,he⟩ := hcontrol x (Or.inl hx)
  have hyend := inverse_ends hy
  have hr : FreeGroup.IsReduced (y⁻¹.toWord ++ [(k,true)]) := by
    apply List.IsChain.append FreeGroup.isReduced_toWord FreeGroup.IsReduced.singleton
    intro a ha b hb hab
    simp only [List.head?_cons, Option.mem_some_iff] at hb
    subst b
    rcases hyend.2 with h | ⟨i,h⟩
    · rw [h] at ha
      simp only [Option.mem_some_iff] at ha
      obtain rfl := ha
      exact False.elim (by simpa using (Nat.ne_of_gt hk).symm hab)
    · rw [h] at ha
      simp only [Option.mem_some_iff] at ha
      obtain rfl := ha
      rfl
  refine ⟨k,hk,?_⟩
  change (y⁻¹ * (s (s x))⁻¹).toWord = _
  rw [he, inv_inv, FreeGroup.toWord_mul, FreeGroup.toWord_of, hr.reduce_eq]

include hcontrol in
theorem division_bounded {x y : Carrier} (hx : bounded x) (hy : bounded y) :
    bounded ((division s).op x y) := by
  obtain ⟨k,_,he⟩ := division_word s hcontrol hx hy
  obtain ⟨j,hj⟩ := (inverse_ends hy).1
  have hn : y⁻¹.toWord ≠ [] := by intro h; simp [h] at hj
  refine Or.inr ⟨⟨j,?_⟩,⟨k,?_⟩⟩
  · rw [he, List.head?_append_of_ne_nil _ hn]
    exact hj
  · rw [he, List.getLast?_append_of_ne_nil _ (by simp)]
    rfl

abbrev Subcarrier := {x : Carrier // bounded x}
@[implicit_reducible] def subDivision : Magma Subcarrier :=
  ⟨fun x y => ⟨(division s).op x.val y.val, division_bounded s hcontrol x.property y.property⟩⟩

def generator : Subcarrier := ⟨FreeGroup.of 0, Or.inl rfl⟩

theorem sub_eval {A : Type} (t : FreeMagma A) (v : A → Subcarrier) :
    (@evalInMagma _ _ (subDivision s hcontrol) v t).val =
      @evalInMagma _ _ (division s) (fun i => (v i).val) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change (division s).op _ _ = _
    rw [ha,hb]
    rfl

include hcontrol in
theorem sub_not_leftQuasigroup : ¬ IsSideQuasigroup .left (subDivision s hcontrol) := by
  intro hQ
  obtain ⟨y,hy⟩ := (hQ generator).2 generator
  have hl := congrArg (fun x : Subcarrier => x.val.toWord.length) hy
  obtain ⟨k,_,he⟩ := division_word s hcontrol generator.property y.property
  change (((division s).op generator.val y.val).toWord).length = _ at hl
  rw [he] at hl
  have hnonempty : y.val⁻¹.toWord ≠ [] := by
    obtain ⟨j,hj⟩ := (inverse_ends y.property).1
    intro h; simp [h] at hj
  have hpos := List.length_pos_iff.mpr hnonempty
  simp only [List.length_append, generator, FreeGroup.toWord_of,
    List.length_singleton] at hl
  omega

/-- A second subset, used for right division: positive first letter different
from the distinguished generator, and negative distinguished last letter. -/
def rightBounded (x : Carrier) : Prop :=
  (∃ k : Nat, 0 < k ∧ x.toWord.head? = some (k,true)) ∧
    x.toWord.getLast? = some (0,false)

@[implicit_reducible] def rightDivision : Magma Carrier :=
  ⟨fun x y => s (y⁻¹ * x⁻¹)⟩

include hcube in
theorem isRightDivision : IsDivision .right (source s) (rightDivision s) := by
  constructor <;> intro x y
  · change (s (s (s (y⁻¹ * x⁻¹))))⁻¹ * y⁻¹ = x
    rw [hcube]
    group
  · change s (y⁻¹ * ((s (s x))⁻¹ * y⁻¹)⁻¹) = x
    have he : y⁻¹ * ((s (s x))⁻¹ * y⁻¹)⁻¹ = s (s x) := by group
    rw [he,hcube]

private theorem right_inverse_ends {x : Carrier} (hx : rightBounded x) :
    x⁻¹.toWord.head? = some (0,true) ∧
    ∃ k : Nat, 0 < k ∧ x⁻¹.toWord.getLast? = some (k,false) := by
  obtain ⟨⟨k,hk,hhead⟩,hlast⟩ := hx
  refine ⟨?_,⟨k,hk,?_⟩⟩
  · simp [FreeGroup.toWord_inv, FreeGroup.invRev, List.head?_reverse, hlast]
  · simp [FreeGroup.toWord_inv, FreeGroup.invRev, List.getLast?_reverse, hhead]

private theorem right_argument {x y : Carrier} (hx : rightBounded x) (hy : rightBounded y) :
    (y⁻¹ * x⁻¹).toWord = y⁻¹.toWord ++ x⁻¹.toWord ∧ rightInput (y⁻¹ * x⁻¹) := by
  have hxend := right_inverse_ends hx
  have hyend := right_inverse_ends hy
  obtain ⟨k,hk,hkhead⟩ := hyend.2
  have hr : FreeGroup.IsReduced (y⁻¹.toWord ++ x⁻¹.toWord) := by
    apply List.IsChain.append FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
    simp only [hkhead,hxend.1,Option.mem_some_iff]
    rintro a rfl b rfl hab
    exact False.elim (Nat.ne_of_gt hk hab)
  have he : (y⁻¹ * x⁻¹).toWord = y⁻¹.toWord ++ x⁻¹.toWord := by
    rw [FreeGroup.toWord_mul,hr.reduce_eq]
  have hxn : x⁻¹.toWord ≠ [] := by intro h; have := hxend.1; simp [h] at this
  have hyn : y⁻¹.toWord ≠ [] := by intro h; have := hyend.1; simp [h] at this
  refine ⟨he,?_,?_⟩
  · rw [he,List.head?_append_of_ne_nil _ hyn]
    exact hyend.1
  · obtain ⟨j,hj,hjlast⟩ := hxend.2
    refine ⟨j,hj,?_⟩
    rw [he,List.getLast?_append_of_ne_nil _ hxn]
    exact hjlast

include htriangle hcontrol in
theorem right_division_word {x y : Carrier} (hx : rightBounded x) (hy : rightBounded y) :
    ∃ k : Nat, 0 < k ∧
      ((rightDivision s).op x y).toWord = (k,true) :: (y⁻¹ * x⁻¹)⁻¹.toWord := by
  let z := y⁻¹ * x⁻¹
  have hz : rightInput z := (right_argument hx hy).2
  obtain ⟨k,hk,he⟩ := hcontrol z (Or.inr hz)
  have hs : s z = FreeGroup.of k * z⁻¹ := by
    have hh := (source_square s htriangle z).symm
    change s z = (s (s z))⁻¹ * z⁻¹ at hh
    simpa only [he, inv_inv] using hh
  have hzhead : ∃ i : Nat, 0 < i ∧ z⁻¹.toWord.head? = some (i,true) := by
    obtain ⟨i,hi,hhead⟩ := hz.2
    exact ⟨i,hi,by simp [FreeGroup.toWord_inv,FreeGroup.invRev,List.head?_reverse,hhead]⟩
  have hr : FreeGroup.IsReduced ([(k,true)] ++ z⁻¹.toWord) := by
    apply List.IsChain.append FreeGroup.IsReduced.singleton FreeGroup.isReduced_toWord
    obtain ⟨i,_,hi⟩ := hzhead
    simp only [List.getLast?_singleton,hi,Option.mem_some_iff]
    rintro a rfl b rfl _
    rfl
  refine ⟨k,hk,?_⟩
  change (s z).toWord = _
  rw [hs,FreeGroup.toWord_mul,FreeGroup.toWord_of]
  exact hr.reduce_eq

include htriangle hcontrol in
theorem right_division_bounded {x y : Carrier} (hx : rightBounded x) (hy : rightBounded y) :
    rightBounded ((rightDivision s).op x y) := by
  obtain ⟨k,hk,he⟩ := right_division_word s htriangle hcontrol hx hy
  have hz := (right_argument hx hy).2
  have hend : (y⁻¹ * x⁻¹)⁻¹.toWord.getLast? = some (0,false) := by
    rw [FreeGroup.toWord_inv]
    simp only [FreeGroup.invRev,List.getLast?_reverse,List.head?_map,hz.1,Option.map_some]
    rfl
  have hn : (y⁻¹ * x⁻¹)⁻¹.toWord ≠ [] := by intro h; rw [h] at hend; contradiction
  refine ⟨⟨k,hk,by simp [he]⟩,?_⟩
  rw [he]
  exact (List.getLast?_append_of_ne_nil [(k,true)] hn).trans hend

abbrev RightSubcarrier := {x : Carrier // rightBounded x}
@[implicit_reducible] def rightSubDivision : Magma RightSubcarrier :=
  ⟨fun x y => ⟨(rightDivision s).op x.val y.val,
    right_division_bounded s htriangle hcontrol x.property y.property⟩⟩

def rightGenerator : RightSubcarrier :=
  ⟨FreeGroup.of 1 * (FreeGroup.of 0)⁻¹, by
    have he : (FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ : Carrier).toWord = [(1,true),(0,false)] := by
      decide
    exact ⟨⟨1,by decide,by simp [he]⟩,by simp [he]⟩⟩

theorem right_sub_eval {A : Type} (t : FreeMagma A) (v : A → RightSubcarrier) :
    (@evalInMagma _ _ (rightSubDivision s htriangle hcontrol) v t).val =
      @evalInMagma _ _ (rightDivision s) (fun i => (v i).val) t := by
  induction t with
  | Leaf => rfl
  | Fork a b ha hb =>
    change (rightDivision s).op _ _ = _
    rw [ha,hb]
    rfl

include htriangle hcontrol in
theorem sub_not_rightQuasigroup :
    ¬ IsSideQuasigroup .right (rightSubDivision s htriangle hcontrol) := by
  intro hQ
  obtain ⟨y,hy⟩ := (hQ rightGenerator).2 rightGenerator
  have hl := congrArg (fun x : RightSubcarrier => x.val.toWord.length) hy
  obtain ⟨k,_,he⟩ := right_division_word s htriangle hcontrol y.property rightGenerator.property
  change (((rightDivision s).op y.val rightGenerator.val).toWord).length = _ at hl
  rw [he,List.length_cons] at hl
  rw [FreeGroup.toWord_inv,FreeGroup.invRev_length,(right_argument y.property rightGenerator.property).1] at hl
  have hypos : 0 < y.val⁻¹.toWord.length := by
    apply List.length_pos_iff.mpr
    intro h
    have := (right_inverse_ends y.property).1
    simp [h] at this
  have hg : rightGenerator.val.toWord.length = 2 := by decide
  have hgi : rightGenerator.val⁻¹.toWord.length = 2 := by
    rw [FreeGroup.toWord_inv,FreeGroup.invRev_length,hg]
  simp only [List.length_append,hg,hgi] at hl
  omega

include hcontrol in
/-- This particular infinite image does not admit any term recovering its
inverse, even with a term chosen specifically for the model. -/
theorem inverse_not_term (t : FreeMagma (Fin 2)) :
    ¬ IsDivision .left (division s) (termMagma (division s) t) := by
  intro hd
  have ht (x y : Subcarrier) :
      ((termMagma (subDivision s hcontrol) t).op x y).val =
        (termMagma (division s) t).op x.val y.val := by
    change (@evalInMagma _ _ (subDivision s hcontrol) _ t).val = _
    rw [sub_eval]
    change @evalInMagma _ _ (division s) _ t = @evalInMagma _ _ (division s) _ t
    congr 1
    funext i
    split <;> rfl
  apply sub_not_leftQuasigroup s hcontrol
  apply sideQuasigroup_of_division (D := termMagma (subDivision s hcontrol) t)
  constructor <;> intro x y <;> apply Subtype.ext
  · change (division s).op x.val ((termMagma (subDivision s hcontrol) t).op x y).val = y.val
    rw [ht]
    exact hd.1 x.val y.val
  · rw [ht]
    exact hd.2 x.val y.val

include htriangle hcontrol in
theorem right_inverse_not_term (t : FreeMagma (Fin 2)) :
    ¬ IsDivision .right (rightDivision s) (termMagma (rightDivision s) t) := by
  intro hd
  have ht (x y : RightSubcarrier) :
      ((termMagma (rightSubDivision s htriangle hcontrol) t).op x y).val =
        (termMagma (rightDivision s) t).op x.val y.val := by
    change (@evalInMagma _ _ (rightSubDivision s htriangle hcontrol) _ t).val = _
    rw [right_sub_eval]
    change @evalInMagma _ _ (rightDivision s) _ t = @evalInMagma _ _ (rightDivision s) _ t
    congr 1
    funext i
    split <;> rfl
  apply sub_not_rightQuasigroup s htriangle hcontrol
  apply sideQuasigroup_of_division (D := termMagma (rightSubDivision s htriangle hcontrol) t)
  constructor <;> intro x y <;> apply Subtype.ext
  · change (rightDivision s).op ((termMagma (rightSubDivision s htriangle hcontrol) t).op x y).val y.val = x.val
    rw [ht]
    exact hd.1 x.val y.val
  · rw [ht]
    exact hd.2 x.val y.val

end Construction

/-- E1719's left-division image fails closure under submagmas. Consequently
no single equation, of any length, can characterize it on arbitrary carriers. -/
theorem no_singleEquation : ¬ SingleEquation .all Law1719 .left := by
  obtain ⟨s,hcube,htriangle,hcontrol⟩ := completion
  rintro ⟨K,hK⟩
  have hd : @satisfies _ _ (division s) K := (hK Carrier (division s) trivial).mpr
    ⟨source s, (@Law1719.models_iff Carrier (source s)).mpr (source_law s hcube htriangle), isDivision s⟩
  have hs : @satisfies _ _ (subDivision s hcontrol) K := by
    intro v
    apply Subtype.ext
    rw [sub_eval,sub_eval]
    exact hd _
  exact sub_not_leftQuasigroup s hcontrol
    (characterizes_sideQuasigroup hK _ (subDivision s hcontrol) trivial hs)

/-- The same completed model also obstructs the right-division image. -/
theorem no_singleEquation_right : ¬ SingleEquation .all Law1719 .right := by
  obtain ⟨s,hcube,htriangle,hcontrol⟩ := completion
  rintro ⟨K,hK⟩
  have hd : @satisfies _ _ (rightDivision s) K := (hK Carrier (rightDivision s) trivial).mpr
    ⟨source s, (@Law1719.models_iff Carrier (source s)).mpr (source_law s hcube htriangle),
      isRightDivision s hcube⟩
  have hs : @satisfies _ _ (rightSubDivision s htriangle hcontrol) K := by
    intro v
    apply Subtype.ext
    rw [right_sub_eval,right_sub_eval]
    exact hd _
  exact sub_not_rightQuasigroup s htriangle hcontrol
    (characterizes_sideQuasigroup hK _ (rightSubDivision s htriangle hcontrol) trivial hs)

end
end Parastrophes.Eq1719ImageObstruction

namespace Parastrophes.Catalogue
open Law
/-- A controlled free-group triangle partition gives a left-division image
with a submagma lacking left division. No equation characterizes the image
on arbitrary carriers. -/
@[parastrophe_result] theorem left_noSingleEquation1719_all :
    ¬ SingleEquation .all Law1719 .left := Eq1719ImageObstruction.no_singleEquation
/-- A second protected set in the same free-group model is closed under right
division but lacks right division itself. The finite negative is proved separately
by triangle trades in `Equation1719FiniteRightImage.lean`. -/
@[parastrophe_result] theorem right_noSingleEquation1719_all :
    ¬ SingleEquation .all Law1719 .right := Eq1719ImageObstruction.no_singleEquation_right
end Parastrophes.Catalogue
