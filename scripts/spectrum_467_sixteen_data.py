"""Reproducible finite normalization data for the E467 order-16 exclusion.

Run this script from the repository root to regenerate Rows/Moves/Refs.lean.
All coverage, permutations, and symmetry properties are checked in Lean.
"""
import json
from pathlib import Path
from spectrum_467_square_search import cycle_types,permutation,first_use_cells
from spectrum_467_1516_search import order16_cycle_types
shapes=cycle_types(16)+[s for s in order16_cycle_types() if s[0]==1]
assert len(shapes)==67
vec=lambda xs:'!['+','.join(map(str,xs))+']'
arr=lambda vs:'#[\n    '+',\n    '.join(vs)+'\n  ][i.val]!'
axes=[permutation(s) for s in shapes]
fixed=[s[0] if i<50 else 1+s[1] for i,s in enumerate(shapes)]
groups=[];moves=[]
for i,s in enumerate(shapes):
 offset=fixed[i];gs=[]
 for j in range(1 if i<50 else 2,len(s)):
  length=s[j];end=offset+length
  for l in s[j+1:]:
   if l!=length:break
   end+=l
  gs.append((offset,end));offset+=length
 groups.append(gs)
# More direct witnesses: rotate the source cycle to target group-start, swapping
# the equal-length cycles when distinct. All other points are fixed.
for i,gs in enumerate(groups):
 axis=axes[i]; blocks=[];offset=0
 for l in shapes[i]:blocks.append(list(range(offset,offset+l)));offset+=l
 mv=[]
 for start,end in gs:
  for z in range(start+1,end):
   src=next(b for b in blocks if z in b);dst=next(b for b in blocks if start in b)
   rot=src[src.index(z):]+src[:src.index(z)]
   p=list(range(16))
   for a,b in zip(rot,dst):
    p[a]=b
    if src!=dst:p[b]=a
   assert p[z]==start and sorted(p)==list(range(16))
   assert all(p[axis[x]]==axis[p[x]] for x in range(16))
   mv.append(dict(start=start,end=end,z=z,perm=p))
 moves.append(mv)
# flatten each case's normalization requests, includes y loop in Encoding
requests=[[(m['start'],m['end'],m['z']) for m in ms] for ms in moves]
sched=[]
for i,k in enumerate(fixed):
 if i<50:sched.append(first_use_cells(16,k))
 else:
  init=[(1,y) for y in range(k)]
  cells=init+[(x,y) for x in range(16) for y in range(16) if (x,y) not in init]
  sched.append(cells)
full=[i<50 and shapes[i][0] in (4,5,6) and all(x==1 for x in shapes[i][1:]) for i in range(67)]
text='''import equational_theories.Spectrum.SmallPairs.ChainRows
import equational_theories.Spectrum.Status
import Mathlib.Data.Fin.VecNotation

/-! Canonical squaring permutations (50), and first rows for the idempotent
case (17). Canonical.lean proves their coverage. Generated finite data are
checked in Lean; none of the following definitions is a proof assumption. -/
namespace Spectrum.E467.OrderSixteen
abbrev Case := Fin 67
abbrev Point := Fin 16

def axis (i : Case) : Point → Point := '''+arr([vec(p) for p in axes])+'''

def inverseAxis (i : Case) : Point → Point := '''+arr([vec([p.index(x) for x in range(16)]) for p in axes])+'''

def isIdempotent (i : Case) : Bool := decide (50 ≤ i.val)
def diagonal (i : Case) (x : Point) : Point := if isIdempotent i then x else axis i x
def inverseDiagonal (i : Case) (x : Point) : Point := if isIdempotent i then x else inverseAxis i x

def fixedCount (i : Case) : ℕ := '''+ '#['+','.join(map(str,fixed))+'][i.val]!'+'''
def scanRow (i : Case) : Point := if isIdempotent i then 1 else 0

def fullFirstUse (i : Case) : Bool := '''+'#['+','.join(str(x).lower() for x in full)+'][i.val]!'+'''

def requests (i : Case) : List (Point × ℕ × Point) := '''+arr(['['+','.join(f'({a},{b},{z})' for a,b,z in req)+']' for req in requests])+'''

private def cellData : String := ''' + json.dumps(''.join(chr(65+x)+chr(65+y) for cs in sched for x,y in cs)) + '''

private def cellDigit (s : String) (j : ℕ) : Point :=
  let v := if h : j < s.utf8ByteSize then
    (s.getUTF8Byte ⟨j⟩ h).toNat - 65 else 0
  ⟨v % 16, Nat.mod_lt _ (by decide)⟩

def cells (i : Case) (j : Fin 256) : Point × Point :=
  (cellDigit cellData (2*(i.val*256+j.val)), cellDigit cellData (2*(i.val*256+j.val)+1))

def fullBound (i : Case) (j : Fin 256) : ℕ :=
  max (fixedCount i) (max (cells i j).1.val (cells i j).2.val + 1)

end Spectrum.E467.OrderSixteen
'''

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / 'equational_theories/Spectrum/Equation467/OrderSixteen'
records = [dict(case=i, return_point=v, shape=shape)
           for i, shape in enumerate(shapes)
           for v in (range(16) if i < 50 and shape[0] in (14,15,16) else [-1])]

def write_data():
    (LEAN / 'Rows.lean').write_text(text)
    perms = [list(range(16))]
    choices = [0] * (67*16*16)
    for i, ms in enumerate(moves):
        for m in ms:
            if m['perm'] not in perms:
                perms.append(m['perm'])
            choices[(i*16+m['start'])*16+m['z']] = perms.index(m['perm'])
    assert len(perms) == 206
    alphabet = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
    replacements = {
        'VALUES': ''.join(chr(65+x) for p in perms for x in p),
        'INVERSES': ''.join(chr(65+p.index(x)) for p in perms for x in range(16)),
        'CHOICES': ''.join(alphabet[v//64]+alphabet[v%64] for v in choices),
    }
    template = (ROOT / 'scripts/templates/Spectrum467Moves.lean.in').read_text()
    for key, value in replacements.items():
        template = template.replace('@'+key+'@', json.dumps(value))
    (LEAN / 'Moves.lean').write_text(template)
    starts = [next(k for k, r in enumerate(records) if r['case'] == i) for i in range(67)]
    template = (ROOT / 'scripts/templates/Spectrum467Refs.lean.in').read_text()
    replacements = {
        'CASES': ','.join(str(r['case']) for r in records),
        'VALUES': ','.join('none' if r['return_point'] < 0 else 'some '+str(r['return_point']) for r in records),
        'STARTS': ','.join(map(str, starts)),
    }
    for key, value in replacements.items():
        template = template.replace('@'+key+'@', value)
    (LEAN / 'Refs.lean').write_text(template)

if __name__ == '__main__':
    write_data()
