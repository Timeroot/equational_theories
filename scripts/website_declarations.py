#!/usr/bin/env python3
"""Index source declaration names and locations before asking Lean to audit them.

This avoids exporting the many compiler-generated helper theorems in certificates.
The Lean stage checks each name against its compiled module before accepting it.
"""
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent


def requests():
    paths = list((ROOT/'equational_theories/Definability').rglob('*.lean'))
    paths += list((ROOT/'equational_theories/Spectrum').rglob('*.lean'))
    paths += [ROOT/'equational_theories/Preorder.lean', ROOT/'equational_theories/MagmaOp.lean']
    result=[]
    for path in sorted(paths):
        text=path.read_text()
        # Preserve lines; source namespaces/sections occur at the left margin.
        text=re.sub(r'/-.*?-/',lambda m:'\n'*m[0].count('\n'),text,flags=re.S)
        scopes=[]
        for line,code in enumerate(text.splitlines(),1):
            code=code.split('--',1)[0]
            if m:=re.match(r'^namespace\s+(\S+)',code):
                scopes.append(('namespace',m[1]))
            elif re.match(r'^(?:noncomputable\s+)?section\b',code):
                scopes.append(('section',''))
            elif re.match(r'^end(?:\s|$)',code):
                if scopes: scopes.pop()
            if m:=re.match(r'^(?:@\[[^\]]*\]\s*)?(?:(private|protected|nonrec)\s+)*(?:theorem|lemma)\s+(\S+)',code):
                name=m[2]
                ns='.'.join(n for kind,n in scopes if kind=='namespace')
                full=name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(filter(None,[ns,name]))
                result.append(dict(name=full,file=str(path.relative_to(ROOT)),line=line,
                                   private=m[1]=='private'))
    return result

if __name__=='__main__':
    out=Path(sys.argv[1] if len(sys.argv)>1 else '/tmp/website-declaration-requests.json')
    data=requests()
    out.write_text(json.dumps(data,separators=(',',':')))
    print(f'Indexed {len(data)} named source theorems ({sum(x["private"] for x in data)} private)')
