#!/usr/bin/env python3
"""Regenerate the small finite encoding and transport lemmas for Cyclic1483.

The saved LRAT file is retained; ordinary builds replay it with bv_check.
To replace that certificate after a deliberate change to the finite query,
use bv_decide? temporarily and retain its new proof as FiniteCertificate.lrat.
"""

from pathlib import Path
rot=lambda x:((x<<1)&7)|(x>>2)
ps=[[0,1,4,6,2,5,3,7],[0,1,4,5,2,3,6,7],[0,1,4,3,2,6,5,7]]
args='a0 a1 a2 a3 a4 a5 a6 a7'
op=lambda x,y:f'(op {args} {x} {y})'
reps=[]
for x in range(8):
 for y in range(8):
  for z in range(8):
   trip=(x,y,z);trip1=(rot(x),rot(y),rot(z));trip2=tuple(map(rot,trip1))
   if trip==min(trip,trip1,trip2):reps.append(trip)
L=['import equational_theories.Spectrum.Equation1486.Encoding8','', '/-! Finite C3 symmetry certificate for an E1485 operation on eight points. -/', 'set_option maxHeartbeats 12000000','set_option maxRecDepth 100000','namespace Definability.Cyclic1483.FiniteCertificate','open Spectrum.FiniteTableEncoding.N8','', 'def rotation (x : BitVec 3) : BitVec 3 := (x <<< 1) ||| (x >>> 2)','']
for i,p in enumerate(ps):L += [f'def reflection{i} (x : BitVec 3) : BitVec 3 := '+''.join(f'if x = {j} then {p[j]} else ' for j in range(7))+str(p[7]),'']
def conj(name,ss):
 L.append(f'def {name} ({args} : BitVec 24) : Prop :=')
 L.append('  '+' ∧\n  '.join(ss));L.append('')
conj('rotationTest',[f'rotation {op(x,y)} = {op(rot(x),rot(y))}' for x in range(8) for y in range(8)])
conj('lawTest',[f'({x} : BitVec 3) = {op(op(y,x),op(x,op(z,y)))}' for x,y,z in reps])
for i,p in enumerate(ps):conj('reflectionTest'+str(i),[f'reflection{i} {op(x,y)} = {op(p[x],p[y])}' for x in range(8) for y in range(8)])
L += [f'theorem certificate ({args} : BitVec 24) :',f'    rotationTest {args} → lawTest {args} →',f'    reflectionTest0 {args} ∨ reflectionTest1 {args} ∨ reflectionTest2 {args} := by','  unfold rotationTest lawTest reflectionTest0 reflectionTest1 reflectionTest2', '  unfold rotation reflection0 reflection1 reflection2 op clip','  bv_decide (config := { timeout := 180, embeddedConstraintSubst := true })','', '#print axioms certificate','end Definability.Cyclic1483.FiniteCertificate']
body = '\n'.join(L)+'\n'
Path('equational_theories/Definability/Cyclic1483/FiniteEncoding.lean').write_text(body.split('theorem certificate')[0]+'end Definability.Cyclic1483.FiniteCertificate\n')
certificate = 'import equational_theories.Definability.Cyclic1483.FiniteEncoding\n\nset_option maxHeartbeats 12000000\nset_option maxRecDepth 100000\nnamespace Definability.Cyclic1483.FiniteCertificate\nopen Spectrum.FiniteTableEncoding.N8\n\n'+body[body.index('theorem certificate'):]
certificate = certificate.replace('bv_decide (config := { timeout := 180, embeddedConstraintSubst := true })', 'bv_check (config := { embeddedConstraintSubst := true }) \"FiniteCertificate.lrat\"')
certificate = certificate.replace('theorem certificate', '@[spectrum_native]\ntheorem certificate', 1)
Path('equational_theories/Definability/Cyclic1483/FiniteCertificate.lean').write_text(certificate)
print('law reps',len(reps))

from pathlib import Path
rot=lambda x:((x<<1)&7)|(x>>2)
rs=list(map(rot,range(8)));ri=list(map(rot,rs))
ps=[[0,1,4,6,2,5,3,7],[0,1,4,5,2,3,6,7],[0,1,4,3,2,6,5,7]]
L=['import equational_theories.Definability.Negative','import equational_theories.Definability.FiniteFlavour','import equational_theories.Spectrum.Equation1486.Encoding8','', 'set_option maxHeartbeats 2000000', 'namespace Definability.Cyclic1483', 'open Spectrum.FiniteTableEncoding.N8','']
def arr(a):return '!['+', '.join(map(str,a))+']'
L += [f'def rotate (x : Fin 8) : Fin 8 := {arr(rs)} x',f'def rotateBack (x : Fin 8) : Fin 8 := {arr(ri)} x','def rotateEquiv : Fin 8 ≃ Fin 8 where','  toFun := rotate','  invFun := rotateBack','  left_inv := by decide +kernel','  right_inv := by decide +kernel','']
for i,p in enumerate(ps):
 L += [f'def reflect{i} (x : Fin 8) : Fin 8 := {arr(p)} x',f'def reflectEquiv{i} : Fin 8 ≃ Fin 8 where',f'  toFun := reflect{i}',f'  invFun := reflect{i}','  left_inv := by decide +kernel','  right_inv := by decide +kernel','']
tab=[[7^(rot(x)&rot(rot(y))) for y in range(8)] for x in range(8)]
L += [f'def operation (x y : Fin 8) : Fin 8 := ({arr([arr(row) for row in tab])} x) y','@[implicit_reducible] def source : Magma (Fin 8) := ⟨operation⟩','', 'theorem source_models : @Equation1483 (Fin 8) source := by decide +kernel','theorem source_rotation : source.IsEndo rotateEquiv := by decide +kernel']
for i in range(3):L+=[f'theorem source_not_reflection{i} : ¬ source.IsEndo reflectEquiv{i} := by decide +kernel']
L+=['','theorem bv_injective : Function.Injective bv := by','  intro a b h','  exact Fin.ext (congrArg BitVec.toNat h)','', 'end Definability.Cyclic1483']
Path('equational_theories/Definability/Cyclic1483/Base.lean').write_text('\n'.join(L)+'\n')

from pathlib import Path
rot=lambda x:((x<<1)&7)|(x>>2)
args=' '.join(f'(rows M {i})' for i in range(8))
reps=[]
for x in range(8):
 for y in range(8):
  for z in range(8):
   t=(x,y,z);t1=tuple(map(rot,t));t2=tuple(map(rot,t1))
   if t==min(t,t1,t2):reps.append(t)
L=['import equational_theories.Definability.Cyclic1483.Base','import equational_theories.Definability.Cyclic1483.FiniteEncoding','', 'set_option maxHeartbeats 12000000','set_option maxRecDepth 100000','namespace Definability.Cyclic1483','open Spectrum.FiniteTableEncoding.N8 FiniteCertificate','', 'theorem bv_rotate (x : Fin 8) : rotation (bv x) = bv (rotate x) := by','  fin_cases x <;> decide +kernel','']
for i in range(3):L += [f'theorem bv_reflect{i} (x : Fin 8) : reflection{i} (bv x) = bv (reflect{i} x) := by','  fin_cases x <;> decide +kernel','']
L += ['theorem rotationTest_of (M : Magma (Fin 8)) (hr : M.IsEndo rotateEquiv) :',f'    rotationTest {args} := by','  have H (x y : Fin 8) : rotation (encoded M (bv x) (bv y)) =', '      encoded M (bv (rotate x)) (bv (rotate y)) := by','    rw [encoded_eq, encoded_eq, bv_rotate]','    exact congrArg bv (hr x y)','  exact ⟨'+', '.join(f'H {x} {y}' for x in range(8) for y in range(8))+'⟩','', 'theorem lawTest_of (M : Magma (Fin 8)) (hm : @Equation1485 (Fin 8) M) :',f'    lawTest {args} := by','  have H (x y z : Fin 8) : bv x = encoded M (encoded M (bv y) (bv x))','      (encoded M (bv x) (encoded M (bv z) (bv y))) := by','    simp only [encoded_eq]','    exact congrArg bv (hm x y z)','  exact ⟨'+', '.join(f'H {x} {y} {z}' for x,y,z in reps)+'⟩','']
for i in range(3):
 L += [f'theorem reflectionTest{i}_to (M : Magma (Fin 8))',f'    (h : reflectionTest{i} {args}) : M.IsEndo reflectEquiv{i} := by',f'  have H (x y : Fin 8) : reflection{i} (encoded M (bv x) (bv y)) =',f'      encoded M (bv (reflect{i} x)) (bv (reflect{i} y)) := by','    rcases h with ⟨'+', '.join(f'h{x}{y}' for x in range(8) for y in range(8))+'⟩','    fin_cases x <;> fin_cases y <;> assumption','  intro x y','  apply bv_injective',f'  change bv (reflect{i} (M.op x y)) = bv (M.op (reflect{i} x) (reflect{i} y))',f'  rw [← bv_reflect{i}, ← encoded_eq, ← encoded_eq]','  exact H x y','']
L+=['end Definability.Cyclic1483']
Path('equational_theories/Definability/Cyclic1483/Bridge.lean').write_text('\n'.join(L)+'\n')
