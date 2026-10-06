#!/usr/bin/env python3
"""Search projective/affine-plane restrictions for idempotent E667 models.

A timeout is unknown. INFEASIBLE only excludes the selected plane restriction,
not arbitrary PBDs or E667 models. Positive block lists are checked independently.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import sys

sys.modules.setdefault('pyarrow', None)
from ortools.sat.python import cp_model


def field(q):
    if q in (8, 16):
        modulus = {8: 11, 16: 19}[q]
        def mul(a, b):
            out = 0
            while b:
                if b & 1:
                    out ^= a
                b >>= 1
                a <<= 1
                if a & q:
                    a ^= modulus
            return out
        return lambda a, b: a ^ b, mul
    if q == 9:
        return (lambda a, b: (a % 3+b % 3) % 3+3*((a//3+b//3) % 3),
                lambda a, b: (a % 3*(b % 3)-a//3*(b//3)) % 3+
                3*((a % 3*(b//3)+a//3*(b % 3)) % 3))
    assert q > 1 and all(q % d for d in range(2, int(q**0.5)+1))
    return lambda a, b: (a+b) % q, lambda a, b: a*b % q


def plane(q, projective=True):
    add, mul = field(q)
    lines = []
    for m in range(q):
        for b in range(q):
            line = [x*q+add(mul(m, x), b) for x in range(q)]
            lines.append(line+([q*q+m] if projective else []))
    for x in range(q):
        lines.append([x*q+y for y in range(q)]+([q*q+q] if projective else []))
    if projective:
        lines.append(list(range(q*q, q*q+q+1)))
    v = q*q+(q+1 if projective else 0)
    pairs = Counter(p for line in lines for p in combinations(sorted(line), 2))
    assert len(pairs) == v*(v-1)//2 and set(pairs.values()) == {1}
    return v, lines


def solve(q, n, seconds, affine=False, workers=1, point_types=False, anchor_line=None):
    from spectrum_667_extended_bounds import extended_constructions
    _, _, _, known = extended_constructions()
    v, lines = plane(q, not affine)
    allowed = sorted(k for k in range(q+2) if k in known)
    m = cp_model.CpModel()
    x = [m.NewBoolVar(f'p_{i}') for i in range(v)]
    m.Add(sum(x) == n)
    # Affine and projective groups act transitively on ordered distinct pairs.
    m.Add(x[0] == 1)
    if anchor_line is None:
        m.Add(x[1] == 1)
    else:
        assert not affine and anchor_line in allowed and n > anchor_line
        # The complement has at most three points, so its projective-line
        # coordinates can always be normalized. Existence of this line size
        # is a separate assumption and is recorded in the search scope.
        assert q+1-anchor_line <= 3
        for j in range(q+1):
            m.Add(x[q*q+j] == int(j < anchor_line))
    selectors = []
    for line in lines:
        k = m.NewIntVarFromDomain(cp_model.Domain.FromValues(allowed), 'line_size')
        m.Add(sum(x[i] for i in line) == k)
        flags = [m.NewBoolVar(f'size_{j}') for j in allowed]
        m.AddExactlyOne(flags)
        m.Add(k == sum(j*b for j,b in zip(allowed,flags)))
        selectors.append(flags)
    # Pair counting is implied by a plane restriction, but is valuable propagation.
    m.Add(sum(k*(k-1)*flags[j] for flags in selectors
              for j,k in enumerate(allowed)) == n*(n-1))
    if point_types:
        def histograms(left, total, at=0):
            if at == len(allowed)-1:
                if left*allowed[at] == total:
                    yield [left]
                return
            for count in range(left+1):
                for tail in histograms(left-count,total-count*allowed[at],at+1):
                    yield [count]+tail
        types = [[selected]+hist for selected in (0,1)
                 for hist in histograms(q+1,n+q*selected)]
        for p in range(v):
            incident = [i for i,line in enumerate(lines) if p in line]
            counts = [m.NewIntVar(0,q+1,'point_count') for _ in allowed]
            for j,count in enumerate(counts):
                m.Add(count == sum(selectors[i][j] for i in incident))
            m.AddAllowedAssignments([x[p]]+counts,types)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = seconds
    s.parameters.num_search_workers = workers
    status = s.Solve(m)
    out = dict(order=n, field_order=q, affine=affine, allowed=allowed,
               status=s.StatusName(status), seconds=s.WallTime(), workers=workers,
               point_types=point_types,
               anchor_line=anchor_line,
               scope='restriction of the specified Desarguesian plane only')
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        selected = [i for i in range(v) if s.Value(x[i])]
        relabel = {p: i for i, p in enumerate(selected)}
        blocks = [[relabel[i] for i in line if i in relabel] for line in lines]
        blocks = [b for b in blocks if len(b) > 1]
        assert len(selected) == n and all(len(b) in known for b in blocks)
        pairs = Counter(p for b in blocks for p in combinations(sorted(b), 2))
        assert len(pairs) == n*(n-1)//2 and set(pairs.values()) == {1}
        out.update(selected=selected, blocks=blocks,
                   block_counts=dict(Counter(map(len, blocks))))
    return out


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('q', type=int)
    p.add_argument('n', type=int)
    p.add_argument('--seconds', type=float, default=60)
    p.add_argument('--affine', action='store_true')
    p.add_argument('--workers', type=int, default=1)
    p.add_argument('--point-types', action='store_true')
    p.add_argument('--anchor-line', type=int)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    result = solve(a.q, a.n, a.seconds, a.affine, a.workers, a.point_types, a.anchor_line)
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    print({k: v for k, v in result.items() if k not in ('selected', 'blocks')})
