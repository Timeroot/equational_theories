#!/usr/bin/env python3
"""Exhaustive finite E63 search, with an idempotent/non-idempotent case split.

Requires python-sat and a CaDiCaL executable. No default search time limit.
UNSAT is a computational result, not a Lean proof. A timeout is never UNSAT.
See docs/63_spectrum_progress.md for the E229 left-division correspondence.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
from itertools import combinations, product
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time

from pysat.formula import CNF
from pysat.card import CardEnc, EncType
from spectrum_63_atp import validate
from spectrum_63_search import partitions
from spectrum_generate import load_equations, satisfies


def cases(n, minimum_fixed_bound=False):
    # If every element is idempotent, L_0 fixes precisely 0.
    # Otherwise choose a non-idempotent element as 0; its L_0-cycle has length 3.
    result = []
    for idem, first, minimum in [(True, 1, 3), (False, 3, 1)]:
        for rest in partitions(n - first, minimum):
            cycles = [first, *rest]
            if minimum_fixed_bound and not idem and cycles.count(1) > 1:
                continue
            name = ('idem-' if idem else 'nonidem-') + '-'.join(map(str, cycles))
            result.append({'name': name, 'idempotent': idem, 'cycles': cycles})
    return sorted(result, key=lambda c: (-len(c['cycles']), c['name']))


def variable(n, x, y, z):
    return 1 + (x * n + y) * n + z


def base_cnf(n):
    cnf = CNF()
    v = lambda x, y, z: variable(n, x, y, z)
    for x, y in product(range(n), repeat=2):
        for group in ([v(x, y, z) for z in range(n)],
                      [v(x, z, y) for z in range(n)],
                      [v(z, x, y) for z in range(n)]):
            cnf.append(group)
            cnf.extend([[-a, -b] for a, b in combinations(group, 2)])
    # A=(y*x=a), B=(y*a=b), C=(b*y=x). E229 and Latin cancellation
    # imply that any two of A,B,C imply the third. The first clause alone
    # encodes E229; the other two are redundant propagation clauses.
    for y, x, a, b in product(range(n), repeat=4):
        av, bv, cv = v(y, x, a), v(y, a, b), v(b, y, x)
        cnf.extend([[-av, -bv, cv], [-av, bv, -cv], [av, -bv, -cv]])
    for x, y, z in product(range(n), repeat=3):
        # L_x^3(x)=x, obtained by setting y=x in R_x=L_x^-2.
        cnf.append([-v(x, x, y), -v(x, y, z), v(x, z, x)])
        if y != z:
            # No translation has a 2-cycle.
            cnf.append([-v(x, y, z), -v(x, z, y)])
    return cnf


def case_cnf(base, n, case, min_fixed=False, min_commuting=False, lex_rows=0,
             idempotent_no_short_cycles=False, fixed_count_consequence=False,
             lex_powers=False, even_columns=False, idempotent_single_cycle=False,
             nonidempotent_cycle_filter=False, commuting_cycles_mod_three=False,
             no_even_identity=False, commuting_triangles=False,
             zero_three_square_involution=False, positive_fixed_short_cycles=False,
             one_fixed_short_cycles=False, all_nonidempotent_short_cycles=False,
             short_cycle_steps=False, all_row_short_cycles=False,
             diagonal_fiber_parity=False):
    # Only append clauses below: sharing the immutable base clauses avoids
    # repeatedly deep-copying the large common Latin/equation encoding.
    cnf = CNF()
    cnf.nv = base.nv
    cnf.clauses = list(base.clauses)
    cnf.comments = list(base.comments)
    if case['idempotent']:
        for x in range(n):
            cnf.append([variable(n, x, x, x)])
    if idempotent_no_short_cycles:
        # Derived from earlier complete refutations of all idempotent first-row
        # types containing a 3- or 4-cycle. These are NOT universal E229 laws.
        # spectrum_63_verify_search.py checks the required dependency cases.
        assert case['idempotent']
        for x, y, z in product(range(n), repeat=3):
            if x != y:
                # Commuting partners are exactly the points in 1- or 3-cycles.
                cnf.append([-variable(n, x, y, z), -variable(n, y, x, z)])
            if y != z:
                # R_x=L_x^-2: a 2-cycle of R_x comes from a 4-cycle of L_x.
                cnf.append([-variable(n, y, x, z), -variable(n, z, x, y)])
    offset = 0
    for length in case['cycles']:
        for i in range(length):
            cnf.append([variable(n, 0, offset + i, offset + (i + 1) % length)])
        offset += length
    assert offset == n
    if min_fixed and not case['idempotent']:
        # Choose 0 among non-idempotent elements with the fewest fixed
        # points of its left translation. This is a global relabeling rule,
        # not an additional law or a restriction on the spectrum.
        fixed = case['cycles'].count(1)
        for x in range(1, n):
            encoding = CardEnc.atleast([variable(n, x, y, y) for y in range(n)],
                                      bound=fixed, top_id=cnf.nv,
                                      encoding=EncType.seqcounter)
            cnf.extend([[variable(n, x, x, x), *clause] for clause in encoding.clauses])
    if fixed_count_consequence:
        # Across all rows there are exactly n fixed points: each column y
        # contains the value y once. If the minimum for non-idempotent rows
        # is 1, every row has at least one and therefore exactly one.
        assert min_fixed and not case['idempotent'] and case['cycles'].count(1) == 1
        for x in range(n):
            fixed = [variable(n, x, y, y) for y in range(n)]
            cnf.append(fixed)
            cnf.extend([[-a, -b] for a, b in combinations(fixed, 2)])
    if min_commuting:
        assert min_fixed
        add_min_commuting(cnf, n, case)
    if lex_rows:
        add_centralizer_lex(cnf, n, case, lex_rows, lex_powers)
    if even_columns:
        add_even_columns(cnf, n)
    if idempotent_single_cycle:
        # Reserve this branch for models with this cycle type at EVERY row.
        # Models having a different row type must remain covered by the other
        # idempotent cases. This is a case-split rule, not a universal identity.
        assert case['idempotent'] and case['cycles'] == [1, n - 1]
        assert all((n - 1) % d for d in range(2, n - 1)), 'Prime cycle length required'
        add_single_cycle_rows(cnf, n)
    if nonidempotent_cycle_filter:
        assert n == 18 and not case['idempotent'] and min_fixed and min_commuting
        assert case['cycles'].count(1) == 0 or fixed_count_consequence
        add_nonidempotent_cycle_filter(cnf, n, case, zero_three_square_involution)
    elif zero_three_square_involution:
        raise AssertionError('The square consequence requires the row-cycle filter')
    if commuting_cycles_mod_three:
        add_commuting_cycles_mod_three(cnf, n)
    if no_even_identity:
        assert n % 2 == 0
        # A row fixing every point is a two-sided identity since R_x=L_x^-2.
        # In an E229 loop, x^2 is the two-sided inverse of x, (x^2)^2=x,
        # and x^2=x only at the identity. Thus a finite loop has odd order.
        for x in range(n):
            cnf.append([-variable(n, x, y, y) for y in range(n)])
    if commuting_triangles:
        add_commuting_triangles(cnf, n)
    if all_row_short_cycles:
        # The separate 103-pattern certificate excludes every remaining
        # idempotent long-cycle row in these same A/B branches.
        assert all_nonidempotent_short_cycles
    if positive_fixed_short_cycles:
        assert n == 18 and nonidempotent_cycle_filter
        if all_nonidempotent_short_cycles:
            assert one_fixed_short_cycles and min_fixed and min_commuting
            assert case['cycles'] in [[3, 3, 3, 3, 3, 3], [3, 3, 4, 4, 4]]
        add_positive_fixed_short_cycles(cnf, n, one_fixed_short_cycles,
                                        all_nonidempotent_short_cycles,
                                        all_row_short_cycles)
    elif one_fixed_short_cycles:
        raise AssertionError('The one-fixed-point extension requires the positive-row filter')
    elif all_nonidempotent_short_cycles:
        raise AssertionError('The non-idempotent extension requires the positive-row filter')
    if short_cycle_steps:
        assert all_nonidempotent_short_cycles
        add_short_cycle_steps(cnf, n, all_row_short_cycles)
    if diagonal_fiber_parity:
        assert all_row_short_cycles
        add_even_diagonal_fibers(cnf, n)
    return cnf


def add_even_parity(cnf, literals):
    """An XOR chain requiring an even number of true literals."""
    if not literals:
        return
    parity = literals[0]
    for lit in literals[1:]:
        cnf.nv += 1
        nxt = cnf.nv
        cnf.extend([[-parity, -lit, -nxt], [parity, lit, -nxt],
                    [parity, -lit, nxt], [-parity, lit, nxt]])
        parity = nxt
    cnf.append([-parity])


def add_even_diagonal_fibers(cnf, n):
    """For even n, assuming ALL rows have only 1/3/4 cycles.

    Every noncommuting pair belongs to a unique five-point block whose
    off-diagonal table is the order-five idempotent E229 table. A block
    contributes four occurrences of each of its values. Commuting
    off-diagonal occurrences come in opposite pairs. Since each value
    occurs n times in a Latin table, its diagonal multiplicity is even.
    See the explicit five-point table in docs/63_spectrum_progress.md.
    """
    assert n % 2 == 0 and cnf.nv >= n ** 3
    for z in range(n):
        add_even_parity(cnf, [variable(n, x, x, z) for x in range(n)])


def add_short_cycle_steps(cnf, n, include_idempotent=False):
    """Expose L_x²(y)=R_x(y) on noncommuting four-cycles.

    Requires every non-idempotent row to have only 1/3/4 cycles. If
    L_x(y) differs from R_x(y)=L_x^-2(y), its cycle is a four-cycle,
    on which L_x²=L_x^-2. Idempotent rows remain exempt.
    """
    for x, y, a, b in product(range(n), repeat=4):
        if a != b:
            cnf.append([*([] if include_idempotent else [variable(n, x, x, x)]),
                        -variable(n, x, y, a), -variable(n, y, x, b),
                        variable(n, x, a, b)])


def add_positive_fixed_short_cycles(cnf, n, include_one=False, all_nonidempotent=False,
                                   include_idempotent=False):
    """Use the separate row-type exclusions, optionally including f=1."""
    assert not include_idempotent or all_nonidempotent
    for x in range(n):
        cnf.nv += 1
        at_most_one = cnf.nv
        fixed = [variable(n, x, y, y) for y in range(n)]
        if all_nonidempotent:
            # In the two remaining minimum-commuting branches, zero-fixed
            # rows also have only 3/4-cycles. Thus only idempotent rows need
            # exemption, irrespective of whether a fixed point is known yet.
            assert include_one
            cnf.append([-at_most_one])
        elif include_one:
            cnf.extend([[-at_most_one, -a] for a in fixed])
        else:
            cnf.extend([[-at_most_one, -a, -b] for a, b in combinations(fixed, 2)])
        for y, z in product(range(n), repeat=2):
            # Exempt idempotent rows and rows below the certified threshold.
            # Otherwise each cycle divides 3 or 4, using R_x=L_x^-2.
            cnf.append([*([] if include_idempotent else [variable(n, x, x, x)]), at_most_one,
                        -variable(n, y, x, z), variable(n, x, y, z),
                        variable(n, z, x, y)])
        if include_one:
            # All noncommuting points are in 4-cycles in an applicable row.
            bits = []
            for y in range(n):
                if x == y:
                    continue
                cnf.nv += 1
                lit = cnf.nv
                bits.append(lit)
                for z in range(n):
                    a, b = variable(n, x, y, z), variable(n, y, x, z)
                    cnf.extend([[-a, -b, -lit], [lit, -a, b]])
            add_guarded_multiple_of_four(cnf, bits,
                                         [*([] if include_idempotent else [variable(n, x, x, x)]),
                                          at_most_one])


def add_guarded_multiple_of_four(cnf, literals, guards):
    """A residue circuit; require residue zero unless an exemption holds."""
    previous = list(range(cnf.nv + 1, cnf.nv + 5))
    cnf.nv += 4
    cnf.extend([[previous[0]], *[[-lit] for lit in previous[1:]]])
    for lit in literals:
        current = list(range(cnf.nv + 1, cnf.nv + 5))
        cnf.nv += 4
        cnf.append(current)
        cnf.extend([[-a, -b] for a, b in combinations(current, 2)])
        for residue in range(4):
            cnf.extend([[-previous[residue], lit, current[residue]],
                        [-previous[residue], -lit, current[(residue + 1) % 4]]])
        previous = current
    cnf.append([*guards, previous[0]])


def add_commuting_triangles(cnf, n):
    """Commutation is constant on the three pairs in a product triangle.

    The partners commuting with x form Fix(L_x^3), invariant under L_x
    and R_x=L_x^-2. For z=x*y this gives C(x,y)=C(x,z)=C(y,z).
    Every noncommuting cycle has length at least four, so a row has either
    zero or at least four noncommuting partners.
    """
    cnf.nv += 1
    truth = cnf.nv
    cnf.append([truth])
    commuting = {(x, x): truth for x in range(n)}
    for x, y in combinations(range(n), 2):
        cnf.nv += 1
        lit = cnf.nv
        commuting[x, y] = commuting[y, x] = lit
        for z in range(n):
            a, b = variable(n, x, y, z), variable(n, y, x, z)
            cnf.extend([[-a, -b, lit], [-lit, -a, b]])
    for x, y, z in product(range(n), repeat=3):
        entry = variable(n, x, y, z)
        a, b, c = commuting[x, y], commuting[x, z], commuting[y, z]
        cnf.extend([[-entry, -a, b], [-entry, a, -b],
                    [-entry, -a, c], [-entry, a, -c]])
    for x in range(n):
        noncommuting = [-commuting[x, y] for y in range(n) if y != x]
        if n <= 4:
            cnf.extend([[-lit] for lit in noncommuting])
            continue
        cnf.nv += 1
        all_commute = cnf.nv
        cnf.extend([[-all_commute, -lit] for lit in noncommuting])
        enc = CardEnc.atleast(noncommuting, bound=4, top_id=cnf.nv,
                              encoding=EncType.seqcounter)
        cnf.extend([[all_commute, *clause] for clause in enc.clauses])


def add_multiple_of_three(cnf, literals):
    """One-hot residue automaton for the number of true literals modulo 3."""
    previous = list(range(cnf.nv + 1, cnf.nv + 4))
    cnf.nv += 3
    cnf.extend([[previous[0]], [-previous[1]], [-previous[2]]])
    for lit in literals:
        current = list(range(cnf.nv + 1, cnf.nv + 4))
        cnf.nv += 3
        cnf.append(current)
        cnf.extend([[-a, -b] for a, b in combinations(current, 2)])
        for residue in range(3):
            cnf.extend([[-previous[residue], lit, current[residue]],
                        [-previous[residue], -lit, current[(residue + 1) % 3]]])
        previous = current
    cnf.append([previous[0]])


def add_commuting_cycles_mod_three(cnf, n):
    """Nonfixed commuting partners are exactly the points in L_x 3-cycles."""
    for x in range(n):
        bits = []
        for y in range(n):
            if x == y:
                bits.append(-variable(n, x, x, x))
                continue
            cnf.nv += 1
            nonfixed_commuting = cnf.nv
            bits.append(nonfixed_commuting)
            cnf.append([-variable(n, x, y, y), -nonfixed_commuting])
            for z in range(n):
                if z == y:
                    continue
                a, b = variable(n, x, y, z), variable(n, y, x, z)
                cnf.extend([[-a, -b, nonfixed_commuting], [-nonfixed_commuting, -a, b]])
        add_multiple_of_three(cnf, bits)


def add_nonidempotent_cycle_filter(cnf, n, case, square_involution=False):
    """Use prior refutations of all other minimum-fixed-point row types.

    This is an order-18 deduction with explicit certificate dependencies.
    With minimum zero the remaining types are 3^6, 3^2 4^3 and 3 5^3.
    With minimum one, every non-idempotent row has type 1 3^3 4^2.
    The verifier checks that the other types were refuted without this filter
    or a global commuting-count choice, so they apply to every minimum row.
    """
    fixed = case['cycles'].count(1)
    assert not square_involution or (n == 18 and fixed == 0)
    minimum_commuting = fixed + 3 * case['cycles'].count(3)
    counts = [10] if fixed else [k for k in [3, 6, 18] if k >= minimum_commuting]
    assert (fixed, minimum_commuting) in [(1, 10), (0, 3), (0, 6), (0, 18)]
    commuting = {}
    for x, y in combinations(range(n), 2):
        cnf.nv += 1
        lit = cnf.nv
        commuting[x, y] = commuting[y, x] = lit
        for z in range(n):
            a, b = variable(n, x, y, z), variable(n, y, x, z)
            cnf.extend([[-a, -b, lit], [-lit, -a, b]])
    for x in range(n):
        if fixed:
            guard = variable(n, x, x, x)
        else:
            cnf.nv += 1
            guard = cnf.nv  # This row has at least one fixed point.
            fixed_lits = [variable(n, x, y, y) for y in range(n)]
            cnf.append([-guard, *fixed_lits])
            cnf.extend([[-lit, guard] for lit in fixed_lits])
        alternatives = []
        for count in counts:
            cnf.nv += 1
            selected = cnf.nv
            alternatives.append(selected)
            enc = CardEnc.equals([commuting[x, y] for y in range(n) if y != x],
                                 bound=count - 1, top_id=cnf.nv,
                                 encoding=EncType.seqcounter)
            cnf.extend([[-selected, *clause] for clause in enc.clauses])
            if count == 3 and square_involution:
                # Checked exclusions of all nonzero values of 1*1 in the
                # canonical 3,5,5,5 case give (x*x)*(x*x)=x for EVERY
                # zero-fixed-point row with three commuting partners.
                cnf.extend([[-selected, -variable(n, x, x, y),
                             variable(n, y, y, x)] for y in range(n)])
        cnf.append([guard, *alternatives])
        if not fixed and minimum_commuting == 18:
            continue  # Commutativity already forces all cycles to divide 3.
        allow_five = not fixed and minimum_commuting == 3
        for y, z in product(range(n), repeat=2):
            # Set z=R_x(y). A cycle divides 3 iff L_x(y)=z, divides
            # 4 iff R_x(z)=y, and divides 5 iff R_x(z)=L_x(y).
            if not allow_five:
                cnf.append([guard, -variable(n, y, x, z),
                            variable(n, x, y, z), variable(n, z, x, y)])
            else:
                for w in range(n):
                    if w != z:
                        cnf.append([guard, -variable(n, y, x, z),
                                    -variable(n, x, y, w), variable(n, z, x, y),
                                    variable(n, z, x, w)])


def add_single_cycle_rows(cnf, n):
    """For prime n-1, force L_x^(n-1)(x+1)=x+1 at every row.

    The orbit length divides the prime n-1. Idempotence and Latin cancellation
    exclude a fixed point other than x, so this orbit contains all other points.
    """
    for x in range(n):
        start = (x + 1) % n
        previous = [variable(n, x, start, z) for z in range(n)]
        for _ in range(2, n - 1):
            current = list(range(cnf.nv + 1, cnf.nv + n + 1))
            cnf.nv += n
            cnf.append(current)
            cnf.extend([[-a, -b] for a, b in combinations(current, 2)])
            for y, z in product(range(n), repeat=2):
                cnf.append([-previous[y], -variable(n, x, y, z), current[z]])
            previous = current
        for y in range(n):
            cnf.append([-previous[y], variable(n, x, y, start)])


def add_even_columns(cnf, n):
    """Every R_y=L_y^-2 is an even permutation; encode inversion parity."""
    def fresh():
        cnf.nv += 1
        return cnf.nv

    less = {}
    for x, y in product(range(n), repeat=2):
        # less[x,y,a] means the value in cell (x,y) is strictly below a.
        less[x, y, 1] = variable(n, x, y, 0)
        for a in range(2, n):
            lit = fresh()
            prev, value = less[x, y, a - 1], variable(n, x, y, a - 1)
            cnf.extend([[-prev, lit], [-value, lit], [-lit, prev, value]])
            less[x, y, a] = lit
    for y in range(n):
        inversions = []
        for r, s in combinations(range(n), 2):
            inv = fresh()
            inversions.append(inv)
            cnf.append([-variable(n, r, y, 0), -inv])
            for a in range(1, n):
                value, lower = variable(n, r, y, a), less[s, y, a]
                cnf.extend([[-value, -inv, lower], [-value, inv, -lower]])
        parity = inversions[0]
        for inv in inversions[1:]:
            nxt = fresh()
            cnf.extend([[-parity, -inv, -nxt], [parity, inv, -nxt],
                        [parity, -inv, nxt], [-parity, inv, nxt]])
            parity = nxt
        cnf.append([-parity])


def centralizer_generators(n, cycles, all_powers=False):
    """Relabelings fixing 0 and commuting with the prescribed first row."""
    blocks, offset = [], 0
    for length in cycles:
        blocks.append(list(range(offset, offset + length)))
        offset += length
    assert offset == n
    generators = []
    previous = {}
    for block in blocks[1:]:
        if len(block) > 1:
            g = list(range(n))
            for i, x in enumerate(block):
                g[x] = block[(i + 1) % len(block)]
            generators.append(g)
        if len(block) in previous:
            g = list(range(n))
            for x, y in zip(previous[len(block)], block):
                g[x], g[y] = y, x
            generators.append(g)
        previous[len(block)] = block
    if all_powers:
        expanded = {}
        identity = list(range(n))
        for g in generators:
            power = g
            while power != identity:
                expanded[tuple(power)] = power
                power = [g[x] for x in power]
        for left, right in combinations(blocks[1:], 2):
            if len(left) == len(right):
                g = list(range(n))
                for x, y in zip(left, right):
                    g[x], g[y] = y, x
                expanded[tuple(g)] = g
        return list(expanded.values())
    return generators


def add_centralizer_lex(cnf, n, case, rows, all_powers=False):
    """Choose a lexicographically least table prefix in its relabeling orbit.

    A finite orbit has a least prefix, so comparisons against these generators
    preserve a representative. The row-0 choice and its cycle labeling are
    preserved by every generator. The transformed table has entry z at (x,y)
    exactly when the old table has entry g(z) at (g(x),g(y)).
    """
    assert 1 <= rows < n
    positions = list(product(range(1, rows + 1), range(n)))
    for g in centralizer_generators(n, case['cycles'], all_powers):
        prefix_equal = None
        for index, (x, y) in enumerate(positions):
            guard = [] if prefix_equal is None else [-prefix_equal]
            for a in range(n):
                for b in range(a):
                    cnf.append([*guard, -variable(n, x, y, a),
                                -variable(n, g[x], g[y], g[b])])
            if index + 1 < len(positions):
                cnf.nv += 1
                next_equal = cnf.nv
                for z in range(n):
                    cnf.append([*guard, -variable(n, x, y, z),
                                -variable(n, g[x], g[y], g[z]), next_equal])
                prefix_equal = next_equal


def add_min_commuting(cnf, n, case):
    """Break ties in the minimum-fixed-point choice by commuting-partner count.

    Since R_x=L_x^-2, x*y=y*x iff L_x^3(y)=y. Thus the first-row cycle
    lengths determine this count. Older cases without these constraints
    remain valid supersets in a mixed exhaustive certificate.
    """
    count = case['cycles'].count(1) + 3 * case['cycles'].count(3)
    if count <= (1 if case['idempotent'] else 3):
        return
    commuting = {}
    for x, y in combinations(range(n), 2):
        cnf.nv += 1
        lit = cnf.nv
        commuting[x, y] = commuting[y, x] = lit
        for z in range(n):
            a, b = variable(n, x, y, z), variable(n, y, x, z)
            cnf.extend([[-a, -b, lit], [-lit, -a, b]])
    fixed = case['cycles'].count(1)
    for x in range(1, n):
        guards = []
        if not case['idempotent']:
            # A non-idempotent row either has more fixed points than row 0,
            # or has at least as many commuting partners. Idempotent rows
            # do not participate in the selection of row 0 in this branch.
            cnf.nv += 1
            more_fixed = cnf.nv
            encoding = CardEnc.atleast([variable(n, x, y, y) for y in range(n)],
                                      bound=fixed + 1, top_id=cnf.nv,
                                      encoding=EncType.seqcounter)
            cnf.extend([[-more_fixed, *clause] for clause in encoding.clauses])
            guards = [variable(n, x, x, x), more_fixed]
        encoding = CardEnc.atleast([commuting[x, y] for y in range(n) if y != x],
                                  bound=count - 1, top_id=cnf.nv,
                                  encoding=EncType.seqcounter)
        cnf.extend([[*guards, *clause] for clause in encoding.clauses])


def dimacs_body(clauses):
    return ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in clauses)


def check_model(n, output):
    assignment = {int(x) for line in output.splitlines() if line.startswith('v ')
                  for x in line[2:].split() if int(x) > 0}
    table = []
    for x in range(n):
        row = []
        for y in range(n):
            values = [z for z in range(n) if variable(n, x, y, z) in assignment]
            assert len(values) == 1, 'Incomplete SAT assignment'
            row.append(values[0])
        table.append(row)
    validate(table, n, 229)
    e63 = [[table[x].index(y) for y in range(n)] for x in range(n)]
    validate(e63, n)
    equations = load_equations()
    assert satisfies(*equations[228], sum(table, []), n)
    assert satisfies(*equations[62], sum(e63, []), n)
    return e63


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=14)
    parser.add_argument('--cadical', type=Path, default=Path('/usr/local/bin/cadical'))
    parser.add_argument('--workdir', type=Path, required=True)
    parser.add_argument('--proofdir', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=12)
    parser.add_argument('--memory-mb', type=int, default=4096)
    parser.add_argument('--proof-limit-mb', type=int, default=2048)
    parser.add_argument('--min-fixed', action='store_true')
    parser.add_argument('--minimum-fixed-bound', action='store_true')
    parser.add_argument('--min-commuting', action='store_true')
    parser.add_argument('--lex-rows', type=int, default=0)
    parser.add_argument('--lex-powers', action='store_true',
                        help='Compare every cycle rotation and equal-cycle swap')
    parser.add_argument('--even-columns', action='store_true',
                        help='Encode the even parity of each right translation')
    parser.add_argument('--seconds', type=int, default=0, help='0 means unlimited')
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    assert args.order >= 3 and 1 <= args.workers <= 36 and args.seconds >= 0
    assert not args.min_commuting or args.min_fixed
    assert not args.minimum_fixed_bound or args.min_fixed
    assert 0 <= args.lex_rows < args.order
    assert not args.lex_powers or args.lex_rows
    args.workdir.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.proofdir:
        args.proofdir.mkdir(parents=True, exist_ok=True)
    report = {'law': 63, 'order': args.order, 'evidence': 'SAT_SOLVER_NOT_LEAN',
              'scope': 'All finite models; complete idempotent/non-idempotent cycle split',
              'started_at': time.time(), 'seconds_per_case': args.seconds,
              'min_fixed': args.min_fixed,
              'minimum_fixed_bound': args.minimum_fixed_bound,
              'min_commuting': args.min_commuting,
              'lex_rows': args.lex_rows,
              'lex_powers': args.lex_powers,
              'even_columns': args.even_columns,
              'solver_version': subprocess.check_output([str(args.cadical), '--version'],
                                                        text=True).strip(),
              'cases': cases(args.order, args.minimum_fixed_bound),
              'attempts': [], 'status': 'PREPARING'}
    if args.resume:
        report = json.loads(args.output.read_text())
        assert report['order'] == args.order
    base = base_cnf(args.order)
    base_body = dimacs_body(base.clauses)
    for case in report['cases']:
        if args.minimum_fixed_bound and not case['idempotent'] and case['cycles'].count(1) == 1:
            case['fixed_count_consequence'] = True
        source = args.workdir / (case['name'] + '.cnf')
        cnf = case_cnf(base, args.order, case, args.min_fixed, args.min_commuting,
                      args.lex_rows, False, case.get('fixed_count_consequence', False),
                      args.lex_powers, args.even_columns)
        contents = (f'p cnf {cnf.nv} {len(cnf.clauses)}\n' + base_body +
                    dimacs_body(cnf.clauses[len(base.clauses):]))
        digest = hashlib.sha256(contents.encode()).hexdigest()
        assert case.get('cnf_sha256', digest) == digest, 'Changed encoding on resume'
        source.write_text(contents)
        case.update(cnf=str(source), cnf_sha256=digest)
    lock = threading.Lock()
    stopped = threading.Event()
    active = {}

    def save():
        p = args.output.with_suffix('.json.tmp')
        p.write_text(json.dumps(report, indent=2) + '\n')
        p.replace(args.output)

    save()
    if args.prepare_only:
        return

    def run(case):
        if stopped.is_set():
            return None
        log = args.workdir / (case['name'] + '.log')
        proof = args.proofdir / (case['name'] + '.drat.gz') if args.proofdir else None
        command = ['prlimit', f'--as={args.memory_mb * 1024**2}',
                   f'--fsize={args.proof_limit_mb * 1024**2}', '--',
                   str(args.cadical)]
        if args.seconds:
            command += ['-t', str(args.seconds)]
        command.append(case['cnf'])
        if proof:
            command.append(str(proof))
        started = time.time()
        with log.open('w') as handle:
            process = subprocess.Popen(command, stdout=handle, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            with lock:
                active[case['name']] = process
                report['active'] = {name: p.pid for name, p in active.items()}
                save()
            exit_code = process.wait()
        output = log.read_text()
        result = {'name': case['name'], 'command': command, 'exit_code': exit_code,
                  'wall_seconds': round(time.time() - started, 3), 'log': str(log),
                  'proof': str(proof) if proof else None}
        if exit_code == 10 and '\ns SATISFIABLE\n' in output:
            result.update(status='VERIFIED_MODEL', e63_table=check_model(args.order, output))
            stopped.set()
        elif exit_code == 20 and '\ns UNSATISFIABLE\n' in output:
            result['status'] = 'UNSAT_NOT_LEAN'
        else:
            result['status'] = 'INTERRUPTED_OR_RESOURCE_LIMIT' if stopped.is_set() or exit_code else 'UNKNOWN'
        with lock:
            active.pop(case['name'])
            report['attempts'].append(result)
            report['active'] = {name: p.pid for name, p in active.items()}
            if result['status'] == 'VERIFIED_MODEL':
                report['witness'] = result['e63_table']
                for p in active.values():
                    try:
                        os.killpg(p.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
            save()
        print(case['name'], result['status'], result['wall_seconds'], flush=True)
        return result

    def interrupt(signum, frame):
        stopped.set()
        for process in list(active.values()):
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass

    signal.signal(signal.SIGTERM, interrupt)
    signal.signal(signal.SIGINT, interrupt)
    completed = {r['name'] for r in report['attempts']
                 if r['status'] in ('UNSAT_NOT_LEAN', 'VERIFIED_MODEL')}
    report['status'] = 'RUNNING'
    save()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(run, case) for case in report['cases']
                   if case['name'] not in completed]
        for future in as_completed(futures):
            future.result()
    completed = {r['name'] for r in report['attempts'] if r['status'] == 'UNSAT_NOT_LEAN'}
    report['status'] = ('VERIFIED_MODEL' if report.get('witness') else
                        'ALL_CASES_UNSAT_NOT_LEAN' if len(completed) == len(report['cases']) else
                        'UNRESOLVED')
    report['finished_at'] = time.time()
    save()
    print(report['status'], flush=True)


if __name__ == '__main__':
    main()
