#!/usr/bin/env python3
"""Evaluate the three eight-point symmetry witnesses against all 4694 laws.

Report satisfied laws and their finite FO classes, and compare with the open
arrows toward E4405 in the current saved audit snapshot. After integrating the
new negative theorems, that last list is expected to shrink to empty.
"""
from pathlib import Path
from itertools import product
import json,sys,time
import numpy as np
sys.path.insert(0,'scripts')
from spectrum_generate import load_equations,variables
q=load_equations();n=8
sources={label:json.loads(Path(path).read_text())['relabeled_model'] for label,path in [('bookend','data/definability_167_4405_separation.json'),('central1483','data/definability_1483_4405_separation.json')]}
s=Path('equational_theories/Definability/Prn_prn8h4a_data.lean').read_text();line=next(l for l in s.splitlines() if l.startswith('def prn8h4aMd1485 :'))
sources['existing1485']=json.loads(line.split(':=')[1].replace('#',''))
b=json.loads(Path('docs/definability_open/snapshot.json').read_text())['boards']['definable/fin']
rep={int(v):int(k) for k,vs in b['classes'].items() for v in vs}
open_to={int(s) for s,rs in b['open_rows'].items() if any(4405 in ts for ts in rs.values())}
cache={};results={}
for label,t in sources.items():
 a=np.array(t,dtype=np.uint8);good=[];st=time.monotonic()
 for law,(l,r) in enumerate(q,1):
  vs=tuple(sorted(variables(l)|variables(r)))
  if vs not in cache:
   grid=np.indices((n,)*len(vs),dtype=np.uint8).reshape(len(vs),-1)
   cache[vs]=dict(zip(vs,grid))
  env=cache[vs]
  def ev(x):return env[x] if isinstance(x,str) else a[ev(x[0]),ev(x[1])]
  if np.array_equal(ev(l),ev(r)):good.append(law)
 classes={rep[i] for i in good};opens=sorted(classes&open_to)
 results[label]=dict(satisfied_laws=good,satisfied_fo_classes=sorted(classes),old_open_to4405=opens,seconds=time.monotonic()-st)
 print(label,'satisfies',len(good),'FOclasses',sorted(classes),'open4405',opens,'sec',time.monotonic()-st,flush=True)
 for c in opens:print(' class',c,'laws',[i for i in good if rep[i]==c],flush=True)
Path('data/definability_klein_four_eight_scan.json').write_text(json.dumps(results,indent=2)+'\n')
