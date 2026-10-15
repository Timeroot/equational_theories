#!/usr/bin/env python3
"""Construct finite term operations using a majority term and pair interpolation.

This is a positive-witness algorithm, not an obstruction test. Every returned
term is evaluated on its entire finite domain. A failed bounded search is
inconclusive. No assumption about a whole equational variety is made.

A term m is a majority term when m(x,x,y) = m(x,y,x) = m(y,x,x) = x.
Such a term makes pairwise interpolation sufficient for term membership:
combine witnesses for S minus {a}, {b}, and {c} using m. At every coordinate of S,
at least two of these three witnesses have the desired value.
"""
from itertools import combinations, product
import time

import numpy as np


def closure(table, seeds, goals=None, limit=4096, deadline=None):
    """Generate a subpower, retaining terms in the original seed variables.

    The returned lookup certifies membership only. In particular, reaching the
    size limit never certifies nonmembership. Duplicate seeds retain their
    original variable indices.
    """
    values, nodes, lookup = [], [], {}
    for i, seed in enumerate(seeds):
        seed = tuple(seed)
        if seed not in lookup:
            lookup[seed] = len(values)
            values.append(seed)
            nodes.append(i)
    goals = set(map(tuple, goals)) if goals is not None else None
    i = 0
    while i < len(values):
        if deadline is not None and time.monotonic() >= deadline:
            break
        if goals is not None and goals <= lookup.keys():
            break
        for j in range(i + 1):
            for a, b in ((i, j), (j, i)):
                value = tuple(table[x][y] for x, y in zip(values[a], values[b]))
                if value not in lookup:
                    lookup[value] = len(values)
                    values.append(value)
                    nodes.append([a, b])
                    if len(values) >= limit:
                        return values, nodes, lookup
        i += 1
    return values, nodes, lookup


class Terms:
    """Term DAG with semantic sharing, evaluated on all input tuples."""

    def __init__(self, table, arity):
        self.table = np.asarray(table, dtype=np.uint8)
        self.arity = arity
        inputs = np.array(list(product(range(len(table)), repeat=arity)), dtype=np.uint8).T
        self.ops = list(inputs)
        self.nodes = list(range(arity))
        self.lookup = {a.tobytes(): i for i, a in enumerate(self.ops)}

    def mul(self, a, b):
        op = self.table[self.ops[a], self.ops[b]]
        key = op.tobytes()
        if key not in self.lookup:
            self.lookup[key] = len(self.ops)
            self.ops.append(op)
            self.nodes.append([a, b])
        return self.lookup[key]

    def subst(self, nodes, root, args):
        # Visit only ancestors of root; closure searches can have many unused nodes.
        needed = {root}
        for i in range(root, -1, -1):
            if i in needed and not isinstance(nodes[i], int):
                needed.update(nodes[i])
        images = {}
        for i in sorted(needed):
            node = nodes[i]
            images[i] = args[node] if isinstance(node, int) else self.mul(
                images[node[0]], images[node[1]])
        return images[root]

    def pack(self, root):
        needed = {root}
        for i in range(root, self.arity - 1, -1):
            if i in needed:
                needed.update(self.nodes[i])
        nodes = list(range(self.arity))
        indices = {i: i for i in range(self.arity)}
        for i in sorted(needed - indices.keys()):
            a, b = self.nodes[i]
            indices[i] = len(nodes)
            nodes.append([indices[a], indices[b]])
        return dict(nodes=nodes, root=indices[root])


def evaluate(table, term, arity):
    """Replay a topologically ordered term DAG independently of the search."""
    table = np.asarray(table, dtype=np.uint8)
    inputs = np.array(list(product(range(len(table)), repeat=arity)), dtype=np.uint8).T
    values = []
    for i, node in enumerate(term['nodes']):
        if isinstance(node, int):
            assert 0 <= node < arity
            values.append(inputs[node])
        else:
            a, b = node
            assert 0 <= a < i and 0 <= b < i
            values.append(table[values[a], values[b]])
    assert 0 <= term['root'] < len(values)
    return values[term['root']].reshape((len(table),) * arity)


def is_majority(table):
    n = len(table)
    return all(table[x, x, y] == x and table[x, y, x] == x and table[y, x, x] == x
               for x, y in product(range(n), repeat=2))


def boolean_majority(table, unary_limit=512, seconds=5):
    """Find a majority term by encoding into Boolean bits and decoding.

    All encodings, Boolean gates, and the decoder must themselves be terms of
    this source algebra. Boolean values need not be source idempotents.
    Failure does not establish that a majority term is absent.
    """
    n = len(table)
    deadline = time.monotonic() + seconds
    # Unary terms fix each source idempotent, so a Boolean encoding cannot
    # distinguish three of them. This only rules out this particular method.
    if sum(table[x][x] == x for x in range(n)) > 2:
        return None
    unary, unodes, ulookup = closure(table, [range(n)], limit=unary_limit, deadline=deadline)
    for a, b in combinations(range(n), 2):
        encodings = [u for u in unary if set(u) <= {a, b}]
        if not encodings:
            continue
        and_value, or_value = (a, a, a, b), (a, b, b, b)
        _, gnodes, gates = closure(table, [(a, a, b, b), (a, b, a, b)],
                                  goals=[and_value, or_value], deadline=deadline)
        if and_value not in gates or or_value not in gates:
            continue
        for bits in combinations(encodings, (n - 1).bit_length()):
            if time.monotonic() >= deadline:
                return None
            if len(set(zip(*bits))) != n:
                continue
            _, dnodes, decoder = closure(table, bits, goals=[range(n)], deadline=deadline)
            if tuple(range(n)) not in decoder:
                continue
            dag = Terms(table, 3)

            def gate(value, x, y):
                return dag.subst(gnodes, gates[value], [x, y])

            outputs = []
            for bit in bits:
                x, y, z = [dag.subst(unodes, ulookup[bit], [i]) for i in range(3)]
                outputs.append(gate(or_value, gate(and_value, x, y),
                                    gate(or_value, gate(and_value, x, z), gate(and_value, y, z))))
            root = dag.subst(dnodes, decoder[tuple(range(n))], outputs)
            result = dag.pack(root)
            assert is_majority(evaluate(table, result, 3))
            return result
    return None


def encoded_majority(table, domain, base_majority, unary_limit=1024, seconds=5):
    """Extend a majority term on a small subset via unary encoding and decoding.

    The subset need not be a subalgebra. Only the majority identities on its
    elements are required; intermediate values of the terms may leave it.
    """
    n = len(table)
    domain = set(domain)
    assert 2 <= len(domain) <= n and domain <= set(range(n))
    base = evaluate(table, base_majority, 3)
    assert all(base[x, x, y] == x and base[x, y, x] == x and base[y, x, x] == x
               for x, y in product(domain, repeat=2))
    deadline = time.monotonic() + seconds
    unary, unodes, lookup = closure(table, [range(n)], limit=unary_limit, deadline=deadline)
    encodings = [u for u in unary if set(u) <= domain]
    arity = 1
    while len(domain) ** arity < n:
        arity += 1
    for bits in combinations(encodings, arity):
        if time.monotonic() >= deadline:
            break
        if len(set(zip(*bits))) != n:
            continue
        _, dnodes, decoder = closure(table, bits, goals=[range(n)], deadline=deadline)
        if tuple(range(n)) not in decoder:
            continue
        dag = Terms(table, 3)
        outputs = []
        for bit in bits:
            values = [dag.subst(unodes, lookup[bit], [i]) for i in range(3)]
            outputs.append(dag.subst(base_majority['nodes'], base_majority['root'], values))
        root = dag.subst(dnodes, decoder[tuple(range(n))], outputs)
        result = dag.pack(root)
        assert is_majority(evaluate(table, result, 3))
        return result
    return None


def interpolate(table, majority, target):
    """Construct a binary term matching target, or reject a failed pair test.

    T(k,i,j) agrees with target on positions 0,...,k-1,i,j. For k>0 use
    m(T(k-1,k-1,i), T(k-1,k-1,j), T(k-1,i,j)). This gives a polynomial-size
    shared term, although expanding it as a tree can be exponential.
    """
    n = len(table)
    assert n >= 2 and is_majority(evaluate(table, majority, 3))
    target = np.asarray(target)
    assert target.shape == (n, n) and np.all((0 <= target) & (target < n))
    size = n * n
    dag = Terms(table, 2)
    cache = {}

    def witness(k, i, j):
        key = (k, i, j)
        if key not in cache:
            if k == 0:
                a, b = divmod(i, n), divmod(j, n)
                goal = (int(target[a]), int(target[b]))
                _, nodes, lookup = closure(table, [(a[0], b[0]), (a[1], b[1])], goals=[goal])
                if goal not in lookup:
                    raise ValueError(f'No term interpolates target at positions {i}, {j}')
                root = dag.subst(nodes, lookup[goal], [0, 1])
            else:
                args = [witness(k - 1, k - 1, i), witness(k - 1, k - 1, j), witness(k - 1, i, j)]
                root = dag.subst(majority['nodes'], majority['root'], args)
            cache[key] = root
        return cache[key]

    result = dag.pack(witness(size - 2, size - 2, size - 1))
    assert np.array_equal(evaluate(table, result, 2), target)
    return result


def check_interpolation(table, majority, target):
    """Replay the compact certificate without expanding the interpolated term.

    The majority DAG certifies closure under pointwise majority. Each generated
    two-coordinate subpower supplies a term matching the target at that pair.
    `Magma.MajorityInterpolation.mem_of_pair_interpolation` is the Lean proof
    of the finite interpolation principle used here. This function checks the
    concrete hypotheses in Python; it is not a Lean proof of these model data.
    """
    n = len(table)
    target = np.asarray(target)
    assert n >= 2 and target.shape == (n, n)
    assert np.all((0 <= target) & (target < n))
    assert is_majority(evaluate(table, majority, 3))
    for i, j in combinations(range(n * n), 2):
        a, b = divmod(i, n), divmod(j, n)
        goal = (int(target[a]), int(target[b]))
        _, _, lookup = closure(table, [(a[0], b[0]), (a[1], b[1])], goals=[goal])
        assert goal in lookup, (i, j, goal)
