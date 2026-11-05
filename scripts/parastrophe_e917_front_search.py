#!/usr/bin/env python3
"""Bounded counterexample searches for E917's 22-operation front-product candidate.

The exact finite permutation reduction, common U-cycle length, and fixed-point
converse are proved in Equation917FrontProduct.lean. Every positive result is
checked against the literal four-variable identity. UNSAT remains external
research evidence, not a Lean theorem.
"""
import argparse,sys,time,json,itertools,multiprocessing as mp
from pathlib import Path
from pysat.formula import CNF
from pysat.solvers import Solver
def encode(n,period,unit=None,symmetry=False):
 cnf=CNF();nv=0;memo={}
 U=list(unit) if unit is not None else [(x//period)*period+(x+1)%period for x in range(n)]
 assert sorted(U)==list(range(n))
 inv=[U.index(x)for x in range(n)]
 def value():
  nonlocal nv
  v=tuple(range(nv+1,nv+n+1));nv+=n;cnf.append(list(v))
  for x,y in itertools.combinations(v,2):cnf.append([-x,-y])
  return v
 m=[[value()for y in range(n)]for x in range(n)]
 fs=[[value()for x in range(n)]for k in range(2)]
 a,b=fs
 for f in fs:
  for k in range(n):
   for x,y in itertools.combinations(range(n),2):cnf.append([-f[x][k],-f[y][k]])
 for x,k in itertools.product(range(n),repeat=2):
  for y,z in itertools.combinations(range(n),2):
   cnf.append([-m[x][y][k],-m[x][z][k]]);cnf.append([-m[y][x][k],-m[z][x][k]])
 def shift(v):return U[v] if isinstance(v,int) else tuple(v[inv[k]]for k in range(n))
 def unary(f,v):
  if isinstance(v,int):return f[v]
  key=('f',id(f),v)
  if key in memo:return memo[key]
  z=value();memo[key]=z
  for x,k in itertools.product(range(n),repeat=2):cnf.append([-v[x],-f[x][k],z[k]])
  return z
 def op(x,y):
  if isinstance(x,int) and isinstance(y,int):return m[x][y]
  key=('m',x,y)
  if key in memo:return memo[key]
  z=value();memo[key]=z
  xx=[(x,[])] if isinstance(x,int) else[(i,[-x[i]])for i in range(n)]
  yy=[(y,[])] if isinstance(y,int) else[(j,[-y[j]])for j in range(n)]
  for i,px in xx:
   for j,py in yy:
    for k in range(n):cnf.append(px+py+[-m[i][j][k],z[k]])
  return z
 def eq(x,y):
  if isinstance(x,int):cnf.append([y[x]])
  elif isinstance(y,int):cnf.append([x[y]])
  else:
   for a,b in zip(x,y):cnf.append([-a,b]);cnf.append([-b,a])
 q=[op(op(x,m[x][x]),x)for x in range(n)]
 for x in range(n):
  eq(op(x,q[x]),U[x])
  if period>1 and unit is None:
   cnf.append([-a[x][x]]);cnf.append([-b[x][x]])
 for x,y in itertools.product(range(n),repeat=2):
  eq(op(y,op(q[x],m[x][y])),a[x])
  eq(m[U[x]][y],unary(b,m[x][y]))
  eq(op(a[x],y),unary(a,op(b[x],y)))
 if symmetry:
  assert unit is None, "Symmetry generators require the standard cycle labels"
  # Lexicographic orbit representatives under generators of the centralizer
  # of the prescribed U permutation. A group-orbit minimum satisfies every
  # one of these inequalities, so no isomorphism class is lost.
  def lex_le(vs,ws):
   nonlocal nv
   nv+=1;active=nv;cnf.append([active])
   for vv,ww in zip(vs,ws):
    if vv==ww:continue
    for i in range(n):
     for j in range(i):cnf.append([-active,-vv[i],-ww[j]])
    nv+=1;nxt=nv;cnf.append([-nxt,active])
    for k in range(n):
     cnf.append([-active,-vv[k],-ww[k],nxt])
     cnf.append([-nxt,-vv[k],ww[k]])
    active=nxt
  flat=[m[x][y]for x,y in itertools.product(range(n),repeat=2)]
  generators=[]
  for c0 in range(n//period):
   p=list(range(n))
   for i in range(period):p[c0*period+i]=c0*period+(i+1)%period
   generators.append(p)
  for c0 in range(n//period-1):
   p=list(range(n))
   for i in range(period):p[c0*period+i]=(c0+1)*period+i;p[(c0+1)*period+i]=c0*period+i
   generators.append(p)
  for p in generators:
   invp=[p.index(k)for k in range(n)]
   trans=[tuple(m[invp[x]][invp[y]][invp[k]]for k in range(n))for x,y in itertools.product(range(n),repeat=2)]
   lex_le(flat,trans)
 return cnf,m,fs,U

def check(m,a,b,U):
 n=len(m);q=[m[m[x][m[x][x]]][x]for x in range(n)]
 assert all(m[x][q[x]]==U[x]for x in range(n))
 for x,y in itertools.product(range(n),repeat=2):
  assert m[y][m[q[x]][m[x][y]]]==a[x]
  assert m[U[x]][y]==b[m[x][y]]
  assert m[a[x]][y]==a[m[b[x]][y]]
 for x,y,v,z in itertools.product(range(n),repeat=4):
  f=m[z][m[q[m[y][v]]][m[m[y][v]][z]]]
  assert m[m[U[y]][v]][m[q[x]][m[x][f]]]==x
 assert any(U[x]!=x for x in range(n))

def worker(conn,n,p,symmetry=False):
 start=time.monotonic();cnf,m,fs,U=encode(n,p,symmetry=symmetry);meta={'variables':cnf.nv,'clauses':len(cnf.clauses)};conn.send(meta)
 with Solver(name='cadical195',bootstrap_with=cnf)as s:
  ans=s.solve();r=dict(meta,status='sat'if ans else'unsat',stats=s.accum_stats())
  if ans:
   true={k for k in s.get_model()if k>0}
   val=lambda v:next(x for x,k in enumerate(v)if k in true)
   tab=[[val(v)for v in row]for row in m];a,b=[[val(v)for v in f]for f in fs]
   check(tab,a,b,U);r.update(table=tab,a=a,b=b,U=U)
 r['seconds']=time.monotonic()-start;conn.send(r);conn.close()

def run(n,p,limit,symmetry=False):
 ctx=mp.get_context('spawn');rc,sc=ctx.Pipe(False);pr=ctx.Process(target=worker,args=(sc,n,p,symmetry));pr.start();sc.close();pr.join(limit)
 r={'order':n,'unit_period':p,'symmetry':'centralizer generators, lexicographic' if symmetry else 'none','time_limit':limit,'status':'timeout'if pr.is_alive()else'error','lean_status':'external research only'}
 if pr.is_alive():pr.terminate();pr.join()
 while rc.poll():
  try:r.update(rc.recv())
  except EOFError:break
 rc.close();return r
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--orders',type=int,nargs='+',default=list(range(2,10)))
 parser.add_argument('--symmetry',action='store_true',help='Use lexicographic centralizer symmetry breaking')
 parser.add_argument('--seconds',type=float,default=60)
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 if any(n<2 for n in args.orders) or args.seconds<=0:parser.error('Orders must be >=2 and seconds positive')
 results=[]
 for n in args.orders:
  for p in range(2,n+1):
   if n%p:continue
   r=run(n,p,args.seconds,args.symmetry);results.append(r);print(n,p,r['status'],r.get('seconds'),flush=True)
   args.output.write_text(json.dumps({'candidate_operations':22,'status':'bounded external research, not a Lean converse','records':results},indent=2)+'\n')
   if r['status']=='sat':sys.exit()
