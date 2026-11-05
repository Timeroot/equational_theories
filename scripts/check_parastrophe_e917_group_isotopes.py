#!/usr/bin/env python3
"""Check the E917 forty-operation candidate on finite group isotopes.

Research computation, not a converse proof. Exhaustive on the listed groups
through order seven; deterministic sampling on three groups of order eight.
Any group isotope is isomorphic to x*y=alpha(x).beta(y), so two input
permutations suffice. The reduced permutation criterion is proved in Lean's
Equation917PowerComparison.lean. Small cases are also checked directly.
"""
import numpy as np,itertools,json,time,sys,argparse
from pathlib import Path

def filter_models(m):
 N,n,_=m.shape;ix=np.arange(N)[:,None];x=np.arange(n)[None,:]
 q=m[ix,m[ix,x,m[ix,x,x]],x];u=m[ix,x,q]
 good=np.any(u!=x,axis=1)&np.all(np.sort(u,axis=1)==x,axis=1)
 ids=np.flatnonzero(good)
 if not len(ids):return [],0
 m=m[ids];q=q[ids];u=u[ids];ix=np.arange(len(m))[:,None];bi=np.arange(len(m))[:,None,None]
 ri=np.argsort(m[:,:,0],axis=1)
 a=m[ix,u[ix,ri],0]
 good=np.all(m[bi,u[:,:,None],np.arange(n)[None,None,:]]==a[bi,m],axis=(1,2))
 ids=ids[good];m=m[good];q=q[good];u=u[good];a=a[good]
 if not len(m):return [],0
 ix=np.arange(len(m))[:,None];bi=np.arange(len(m))[:,None,None]
 li=np.argsort(m[:,0,:],axis=1);b=m[ix,0,a[ix,li]]
 good=np.all(m[bi,np.arange(n)[None,:,None],a[:,None,:]]==b[bi,m],axis=(1,2))
 ids=ids[good];m=m[good];q=q[good];u=u[good];a=a[good];b=b[good]
 if not len(m):return [],0
 ix=np.arange(len(m))[:,None];bi=np.arange(len(m))[:,None,None]
 ri=np.argsort(m[:,:,0],axis=1);V=a[ix,a[ix,b]];c=m[ix,V[ix,ri],0]
 good=np.all(m[bi,V[:,:,None],np.arange(n)[None,None,:]]==c[bi,m],axis=(1,2))
 ids=ids[good];m=m[good];q=q[good];u=u[good];a=a[good];b=b[good];c=c[good]
 if not len(m):return [],0
 ix=np.arange(len(m))[:,None];bi=np.arange(len(m))[:,None,None]
 H=m[bi,q[:,:,None],m]
 frame=m[bi,c[:,None,:],H]
 good=np.all(frame==np.arange(n)[None,:,None],axis=(1,2))
 return [(int(ids[i]),m[i].tolist(),a[i].tolist(),b[i].tolist(),c[i].tolist())for i in np.flatnonzero(good)],len(m)

def groups():
 for n in [1,2,3,4,5,6,7]:yield 'C'+str(n),np.add.outer(np.arange(n),np.arange(n))%n,None
 yield 'V4',np.bitwise_xor.outer(np.arange(4),np.arange(4)),None
 ps=list(itertools.permutations(range(3)));mp={v:i for i,v in enumerate(ps)}
 yield 'S3',np.array([[mp[tuple(a[b[i]]for i in range(3))]for b in ps]for a in ps]),None
 pts=list(itertools.product(range(4),range(2)));mp={v:i for i,v in enumerate(pts)}
 yield 'D8',np.array([[mp[((a+(-1)**b*c)%4,(b+d)%2)]for c,d in pts]for a,b in pts]),200000
 yield 'C8',np.add.outer(np.arange(8),np.arange(8))%8,200000
 yield 'C2^3',np.bitwise_xor.outer(np.arange(8),np.arange(8)),200000


def direct_bad(m):
    count,n,_=m.shape
    ix=np.arange(count)[:,None]
    points=np.arange(n)[None,:]
    q=m[ix,m[ix,points,m[ix,points,points]],points]
    u=m[ix,points,q]
    x,y,z,w,v=np.indices((n,n,n,n,n)).reshape(5,-1)
    left=m[ix,m[ix,u[ix,u[:,w]],m[ix,u[:,z],y]],v]
    inner=m[ix,m[ix,w,m[ix,z,y]],v]
    result=m[ix,left,m[ix,q[:,x],m[ix,x,inner]]]
    return np.flatnonzero(np.all(result==x,axis=1)&np.any(u!=points,axis=1)).tolist()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    reports=[]
    rng=np.random.default_rng(917)
    for name,g,cap in groups():
        start=time.monotonic()
        n=len(g)
        perms=np.array(list(itertools.permutations(range(n))))
        N=len(perms)
        total=N*N if cap is None else cap
        bad=[]
        frames=0
        for lo in range(0,total,2048):
            size=min(2048,total-lo)
            if cap is None:
                ids=np.arange(lo,lo+size)
                aa,bb=ids//N,ids%N
            else:
                aa=rng.integers(N,size=size)
                bb=rng.integers(N,size=size)
            m=g[perms[aa,:,None],perms[bb,None,:]]
            bs,cnt=filter_models(m)
            if n<=4:
                assert [r[0] for r in bs]==direct_bad(m), 'Reduced/direct checks disagree'
            frames+=cnt
            for i,tab,a,b,c in bs:
                bad.append({'table':tab,'a':a,'b':b,'c':c,
                            'alpha':perms[aa[i]].tolist(),'beta':perms[bb[i]].tolist()})
            if bad:
                break
        report={'group':name,'order':n,'pairs':min(lo+2048,total),
                'exhaustive':cap is None,'nontrivial_U_pre_frames':frames,
                'counterexamples':bad,'direct_check':n<=4}
        reports.append(report)
        print(name,report['pairs'],'pairs;',len(bad),'counterexamples;',
              round(time.monotonic()-start,2),'seconds',file=sys.stderr,flush=True)
        if bad:
            break
    args.output.write_text(json.dumps({'status':'bounded Python research; not a Lean converse',
        'candidate_operations':40,'records':reports},indent=2)+'\n')


if __name__=='__main__':
    main()
