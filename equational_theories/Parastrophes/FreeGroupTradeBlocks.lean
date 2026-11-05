import equational_theories.Parastrophes.GroupTriangleTrades
import equational_theories.Parastrophes.FreeGroupWordCones

/-!
# Protected words for noncommutative triangle trades

The first coordinate starts and ends at generator 0; the second starts and
ends at nonzero generators. Both last letters are positive. A trade with a
fresh nonzero generator has precisely one point in this protected region:
its designated input. This prevents old orbits from meeting new orbits.
-/
namespace Parastrophes.FreeGroupTradeBlocks
open FreeGroupWordCones GroupTriangleTrades

def Good (x : Word × Word) := ZeroCone x.1 ∧ PositiveCone x.2

private theorem not_zero_head {x : Word} {i : Nat} {b : Bool}
    (hi : i ≠ 0) (hh : x.toWord.head? = some (i,b)) : ¬ ZeroCone x := by
  rintro ⟨⟨j,c,hj,h⟩,_⟩
  rw [hh] at h
  have he := congrArg (fun z : Option (Nat × Bool) => z.map Prod.fst) h
  simp only [Option.map_some,Option.some.injEq] at he
  exact hi (he.trans hj)

private theorem not_zero_last {x : Word} {i : Nat} {b : Bool}
    (hi : i ≠ 0) (hh : x.toWord.getLast? = some (i,b)) : ¬ ZeroCone x := by
  rintro ⟨_,⟨j,hj,h⟩⟩
  rw [hh] at h
  have he := congrArg (fun z : Option (Nat × Bool) => z.map Prod.fst) h
  simp only [Option.map_some,Option.some.injEq] at he
  exact hi (he.trans hj)

/-- Normal forms for the first coordinates of the nine old-orbit points. -/
def first (a b c : Word) (i j : Fin 3) : Word :=
  if i=0 then
    if j=0 then a else if j=1 then b else a⁻¹*b⁻¹
  else if i=1 then
    if j=0 then c else if j=1 then a⁻¹*b⁻¹*c*b⁻¹ else c⁻¹*b*c⁻¹*b*a
  else
    if j=0 then a⁻¹*c⁻¹ else if j=1 then c⁻¹*b*a else c*b⁻¹*c

theorem first_eq (a b c : Word) (i j : Fin 3) :
    (orbit (row (a,b) c i) j).1 = first a b c i j := by
  fin_cases i <;> fin_cases j <;> simp [orbit,row,rotate,first] <;> group

/-- Apart from the designated input, all eight points lie outside the
protected region. The endpoint calculations do not enumerate group elements. -/
theorem outside {a b : Word} {k : Nat}
    (ha : ZeroCone a) (hb : PositiveCone b) (hk : 0 < k) (hf : Fresh k b)
    (i j : Fin 3) (hij : i ≠ 0 ∨ j ≠ 0) :
    ¬ ZeroCone (orbit (row (a,b) (FreeGroup.of k) i) j).1 := by
  obtain ⟨⟨_,ba,rfl,hah⟩,⟨_,rfl,hal⟩⟩ := ha
  obtain ⟨⟨ib,bb,hib,hbh⟩,⟨jb,hjb,hbl⟩⟩ := hb
  let c : Word := FreeGroup.of k
  have ch : c.toWord.head? = some (k,true) := by simp [c]
  have cl : c.toWord.getLast? = some (k,true) := by simp [c]
  have hki : ib ≠ k := fresh_head hf hbh
  have hkj : jb ≠ k := fresh_last hf hbl
  have ab := join_ends (inv_head hal) (inv_last hah) (inv_head hbl) (inv_last hbh)
    (show 0=jb → (!ba)=(!true) by omega)
  have abc := join_ends ab.1 ab.2 ch cl (fun h => (hki h).elim)
  have abcb := join_ends abc.1 abc.2 (inv_head hbl) (inv_last hbh)
    (fun h => (hkj h.symm).elim)
  have cb := join_ends (inv_head cl) (inv_last ch) hbh hbl
    (fun h => (hki h.symm).elim)
  have cbc := join_ends cb.1 cb.2 (inv_head cl) (inv_last ch)
    (fun h => (hkj h).elim)
  have cbcb := join_ends cbc.1 cbc.2 hbh hbl (fun h => (hki h.symm).elim)
  have cbcba := join_ends cbcb.1 cbcb.2 hah hal (show jb=0 → true=ba by omega)
  have ac := join_ends (inv_head hal) (inv_last hah) (inv_head cl) (inv_last ch)
    (show 0=k → (!ba)=(!true) by omega)
  have cba := join_ends cb.1 cb.2 hah hal (show jb=0 → true=ba by omega)
  have cb' := join_ends ch cl (inv_head hbl) (inv_last hbh)
    (fun h => (hkj h.symm).elim)
  have cbc' := join_ends cb'.1 cb'.2 ch cl (fun h => (hki h).elim)
  rw [first_eq]
  change ¬ ZeroCone (first a b c i j)
  fin_cases i <;> fin_cases j <;> simp only [first,Fin.isValue] at hij ⊢
  · exact (hij.elim (fun h => h rfl) (fun h => h rfl)).elim
  · exact not_zero_last (by omega) hbl
  · exact not_zero_last (by omega) ab.2
  · exact not_zero_head (by omega) ch
  · exact not_zero_last (by omega) abcb.2
  · exact not_zero_head (by omega) cbcba.1
  · exact not_zero_last (by omega) ac.2
  · exact not_zero_head (by omega) cba.1
  · exact not_zero_head (by omega) cbc'.1

end Parastrophes.FreeGroupTradeBlocks
