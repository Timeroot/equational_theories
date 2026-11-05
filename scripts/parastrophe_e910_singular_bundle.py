#!/usr/bin/env python3
"""Search singular affine bundles over saved E910 division images.

Coefficients are signed monomials in an indeterminate. E427 reduces to exact
coefficient cancellation, encoded by integer exponents and Boolean signs. A
positive right exponent makes the specialization at zero lose row injectivity,
while every nonzero parameter retains it over a field. Found assignments need
independent checking and Lean formalization before catalogue registration.
"""
import argparse,json,time,itertools
from pathlib import Path
import z3

def solve(base,limit=20,zeros=False):
 n=len(base);S=z3.Solver();S.set(timeout=limit*1000)
 ae=[[z3.Int(f'a_{i}_{j}')for j in range(n)]for i in range(n)]
 be=[[z3.Int(f'b_{i}_{j}')for j in range(n)]for i in range(n)]
 an=[[z3.Bool(f'an_{i}_{j}')for j in range(n)]for i in range(n)]
 bn=[[z3.Bool(f'bn_{i}_{j}')for j in range(n)]for i in range(n)]
 az=[[z3.Bool(f'az_{i}_{j}')if zeros else z3.BoolVal(False)for j in range(n)]for i in range(n)]
 for i,j in itertools.product(range(n),repeat=2):S.add(ae[i][j]>=0,ae[i][j]<=12,be[i][j]>=0,be[i][j]<=4)
 S.add(z3.Or([be[i][j]>0 for i,j in itertools.product(range(n),repeat=2)]))
 def parity(bits):
  v=z3.BoolVal(False)
  for b in bits:v=z3.Xor(v,b)
  return v
 def one(terms):
  alts=[]
  for i in range(3):
   j,k=[t for t in range(3)if t!=i]
   e,s,z=terms[i];f,t,w=terms[j];g,u,v=terms[k]
   alts.append(z3.And(z3.Not(z),e==0,z3.Not(s),z3.Or(z3.And(w,v),z3.And(z3.Not(w),z3.Not(v),f==g,t!=u))))
  return z3.Or(alts)
 for i,j in itertools.product(range(n),repeat=2):
  k=base[i][j];l=base[i][k];m=base[j][l];assert base[i][m]==i
  S.add(z3.Not(az[j][l]))
  S.add(ae[j][l]==be[j][l]+be[i][k]+be[i][j],an[j][l]==z3.Not(parity([bn[j][l],bn[i][k],bn[i][j]])))
  t1=(ae[i][m],an[i][m],az[i][m])
  t2=(be[i][m]+be[j][l]+ae[i][k],parity([bn[i][m],bn[j][l],an[i][k]]),az[i][k])
  t3=(be[i][m]+be[j][l]+be[i][k]+ae[i][j],parity([bn[i][m],bn[j][l],bn[i][k],an[i][j]]),az[i][j])
  S.add(one([t1,t2,t3]))
 st=time.monotonic();ans=S.check();r={'order':n,'zeros':zeros,'status':str(ans),'seconds':time.monotonic()-st}
 if ans==z3.sat:
  model=S.model();v=lambda x: model.eval(x,model_completion=True)
  A=[[None if z3.is_true(v(az[i][j]))else [-1 if z3.is_true(v(an[i][j]))else 1,v(ae[i][j]).as_long()]for j in range(n)]for i in range(n)]
  B=[[[-1 if z3.is_true(v(bn[i][j]))else 1,v(be[i][j]).as_long()]for j in range(n)]for i in range(n)]
  r.update(base=base,A=A,B=B)
  for T in [2,3,5]:
   aa=[[0 if x is None else x[0]*T**x[1]for x in row]for row in A];bb=[[x[0]*T**x[1]for x in row]for row in B]
   for i,j in itertools.product(range(n),repeat=2):
    k=base[i][j];l=base[i][k];m=base[j][l]
    assert aa[i][m]+bb[i][m]*bb[j][l]*(aa[i][k]+bb[i][k]*aa[i][j])==1
    assert aa[j][l]+bb[j][l]*bb[i][k]*bb[i][j]==0
 return r
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--input',type=Path,default=Path('data/parastrophes/e910_e714_images_20261102.json'))
 parser.add_argument('--output',type=Path,required=True)
 parser.add_argument('--seconds',type=int,default=30)
 args=parser.parse_args()
 if args.seconds<=0:parser.error('Time limit must be positive')
 sources=json.loads(args.input.read_text())['sources']['910']['tables']
 bases=[[[0,1],[1,0]]]+[[[row.index(y)for y in range(len(row))]for row in m]for m in sources]
 out=[]
 for zeros in [False,True]:
  for i,base in enumerate(bases):
   r=solve(base,args.seconds,zeros);r['index']=i;out.append(r);print(i,len(base),zeros,r['status'],r['seconds'],flush=True)
   args.output.write_text(json.dumps(out,indent=2)+'\n')
   if r['status']=='sat':raise SystemExit()
