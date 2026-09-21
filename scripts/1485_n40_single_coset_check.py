#!/usr/bin/env python3
"""Exclude the saturated order-40, two-single-coset E1485 branch.

This is exact enumeration of 10,368 linear systems with 64 binary variables,
not a search over magma tables, and uses only the Python standard library.
There are 144 consistent systems.  Their forced partial multiplication
tables fail one of two explicit families of E1485 identity instances.
No conjectural spectrum statement is an input.
"""

from collections import Counter
from itertools import permutations, product
from time import perf_counter


# V=F_2^2, represented by 0,1,2,3.  A matrix is its two column images.
VALUES = range(4)
IDENTITY = (1, 2)
GL2 = tuple((a, b) for a, b in product(range(1, 4), repeat=2) if a != b)
OMEGAS = ((2, 3), (3, 1))
COEFFICIENT_MASK = (1 << 64) - 1


def apply(matrix, value):
    return (matrix[0] if value & 1 else 0) ^ (matrix[1] if value & 2 else 0)


def compose(left, right):
    return apply(left, right[0]), apply(left, right[1])


def add(left, right):
    return left[0] ^ right[0], left[1] ^ right[1]


def inverse(matrix):
    return next(other for other in GL2 if compose(matrix, other) == IDENTITY)


def variable_p(i, j):
    return 2 * (4 * i + j)


def variable_q(i, j):
    return 32 + 2 * (4 * i + j)


def linear_image(variable, matrix):
    """The two binary row masks for matrix times a two-bit variable."""
    return tuple(
        sum(1 << (variable + j) for j in range(2) if matrix[j] & (1 << bit))
        for bit in range(2)
    )


def equations(linear_h, omega, u_matrix, v_matrix, offsets):
    """Equations (3) in the note; bit 64 stores the right-hand side."""
    w_matrix = compose(linear_h, omega)
    for i, j, k in product(VALUES, repeat=3):
        first = linear_image(variable_p(i, j), u_matrix)
        second = linear_image(variable_q(i, j), w_matrix)
        third = linear_image(variable_p(j, k), linear_h)
        for bit in range(2):
            yield first[bit] ^ second[bit] ^ third[bit] ^ (
                ((offsets[k] >> bit) & 1) << 64
            )
        first = linear_image(variable_p(i, j), IDENTITY)
        second = linear_image(variable_q(i, j), v_matrix)
        third = linear_image(variable_q(k, i), IDENTITY)
        rhs = apply(linear_h, k)
        for bit in range(2):
            yield first[bit] ^ second[bit] ^ third[bit] ^ (((rhs >> bit) & 1) << 64)


def solve(rows):
    """Return rank and a solution, or None for an inconsistent system.

    Free variables, if any, are set to zero.  The caller requires rank 64
    for every consistent system, so no other solutions are discarded.
    """
    pivots = {}
    for row in rows:
        while row & COEFFICIENT_MASK:
            pivot = (row & COEFFICIENT_MASK).bit_length() - 1
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
        else:
            if row:
                return None
    value = 0
    for pivot, row in sorted(pivots.items()):
        parity = (row >> 64) ^ (row & COEFFICIENT_MASK & value).bit_count()
        if parity & 1:
            value |= 1 << pivot
    return len(pivots), value


def a_vertex(i, j):
    return 4 + 4 * i + j


def b_vertex(i):
    return 20 + i


def t_vertex(p, q):
    return 24 + 4 * p + q


def forced_table(p, q, linear_h, omega, r_profiles, s_profiles):
    """All products except Z*T and T*Z, by the formulas in the note."""
    h_label = lambda pp, qq: apply(linear_h, pp ^ apply(omega, qq))
    inverse_h = inverse(linear_h)
    inverse_w = inverse(compose(linear_h, omega))
    by_profile = {(p[i][j], q[i][j]): a_vertex(i, j) for i, j in product(VALUES, repeat=2)}
    assert len(by_profile) == 16
    assert all(len({p[i][j] for i in VALUES}) == 4 for j in VALUES)
    assert all(len(set(row)) == 4 for row in q)
    table = {}

    for i, j, k, ell in product(VALUES, repeat=4):
        table[a_vertex(i, j), a_vertex(k, ell)] = (
            b_vertex(j) if j == k else t_vertex(p[k][ell], q[i][j])
        )
        table[t_vertex(i, j), t_vertex(k, ell)] = (
            i ^ j if i ^ j == h_label(k, ell) else by_profile[i, ell]
        )
    for i, j, k in product(VALUES, repeat=3):
        table[a_vertex(i, j), b_vertex(k)] = t_vertex(r_profiles[k][q[i][j]], q[i][j])
        table[b_vertex(k), a_vertex(i, j)] = t_vertex(p[i][j], s_profiles[k][p[i][j]])
        table[b_vertex(i), t_vertex(j, k)] = a_vertex(i, q[i].index(k))
        row = next(row for row in VALUES if p[row][k] == i)
        table[t_vertex(i, j), b_vertex(k)] = a_vertex(row, k)
        table[i, a_vertex(j, k)] = t_vertex(
            p[j][k], apply(inverse_w, i ^ apply(linear_h, p[j][k]))
        )
        table[a_vertex(j, k), i] = t_vertex(i ^ q[j][k], q[j][k])
    for i, j in product(VALUES, repeat=2):
        table[b_vertex(i), b_vertex(j)] = a_vertex(i, j)
        table[h_label(i, j), i ^ j] = t_vertex(i, j)
        table[i, b_vertex(j)] = next(
            t_vertex(r_profiles[j][qq], qq)
            for qq in VALUES if h_label(r_profiles[j][qq], qq) == i
        )
        table[b_vertex(j), i] = next(
            t_vertex(pp, s_profiles[j][pp])
            for pp in VALUES if pp ^ s_profiles[j][pp] == i
        )
    for i, j, pp, qq in product(VALUES, repeat=4):
        aa, tt = a_vertex(i, j), t_vertex(pp, qq)
        if qq == s_profiles[j][pp]:
            table[aa, tt] = b_vertex(j)
        else:
            row = next(row for row in VALUES if p[row][i] == pp)
            output_p = apply(inverse_h, p[i][j] ^ q[row][i]) ^ apply(omega, q[i][j])
            table[aa, tt] = t_vertex(output_p, q[i][j])
        if pp == r_profiles[i][qq]:
            table[tt, aa] = b_vertex(i)
        else:
            column = q[j].index(qq)
            output_q = h_label(p[j][column], q[i][j]) ^ p[i][j]
            table[tt, aa] = t_vertex(p[i][j], output_q)
    assert len(table) == 1472
    return table


def mixed_violation(table):
    """A known W or dual-W violation with x in A, y in B, z in Z."""
    for x, y, z in product(range(4, 20), range(20, 24), VALUES):
        if table[table[y, x], table[x, table[z, y]]] != x:
            return x, y, z, False
        if table[table[table[y, z], x], table[x, y]] != x:
            return x, y, z, True
    return None


def central_top_violation(table, linear_h, omega):
    """Check four candidates for z0*t00 against W(t00,z0,zj).

    Ignore the instance j=0, whose last product may still be unknown.
    This is a necessary-condition check, not an arbitrary completion of
    the 128 still-unknown products.
    """
    x, y = t_vertex(0, 0), 0
    candidates = {
        t_vertex(pp, qq) for pp, qq in product(VALUES, repeat=2)
        if apply(linear_h, pp ^ apply(omega, qq)) == y
    }
    for z in range(1, 4):
        inner = table[x, table[z, y]]
        assert 4 <= inner < 20
        candidates = {candidate for candidate in candidates if table[candidate, inner] == x}
    return not candidates


def main():
    started = perf_counter()
    counts = Counter()
    consistent_slopes = set()
    last_two = []
    for linear_h, omega, u_matrix, v_matrix in product(GL2, OMEGAS, GL2, GL2):
        slope_s = add(IDENTITY, u_matrix)
        slope_r = add(omega, compose(inverse(linear_h), v_matrix))
        r_profiles = tuple(tuple(apply(slope_r, qq) ^ k for qq in VALUES) for k in VALUES)
        for offsets in permutations(VALUES):
            counts["systems"] += 1
            result = solve(equations(linear_h, omega, u_matrix, v_matrix, offsets))
            if result is None:
                counts["inconsistent"] += 1
                continue
            rank, value = result
            assert rank == 64, "A non-unique system requires further analysis"
            p = [[(value >> variable_p(i, j)) & 3 for j in VALUES] for i in VALUES]
            q = [[(value >> variable_q(i, j)) & 3 for j in VALUES] for i in VALUES]
            assert all(((row & COEFFICIENT_MASK & value).bit_count() ^ (row >> 64)) & 1 == 0
                       for row in equations(linear_h, omega, u_matrix, v_matrix, offsets))
            s_profiles = tuple(tuple(apply(slope_s, pp) ^ offsets[k] for pp in VALUES) for k in VALUES)
            counts["unique_solutions"] += 1
            consistent_slopes.add((linear_h, omega, u_matrix, v_matrix))
            table = forced_table(p, q, linear_h, omega, r_profiles, s_profiles)
            if mixed_violation(table) is not None:
                counts["mixed_identity_exclusions"] += 1
                continue
            assert central_top_violation(table, linear_h, omega)
            counts["central_top_exclusions"] += 1
            last_two.append((linear_h, omega, u_matrix, v_matrix, offsets))
    assert counts == Counter(systems=10368, inconsistent=10224, unique_solutions=144,
                             mixed_identity_exclusions=142, central_top_exclusions=2)
    assert len(consistent_slopes) == 36
    assert last_two == [(omega, omega, omega, IDENTITY, tuple(apply(omega, k) for k in VALUES))
                        for omega in OMEGAS]
    print("Order 40, |A5|=16, both A-profile families single V4 cosets: EXCLUDED")
    print(dict(counts))
    print(f"Consistent slope quadruples: {len(consistent_slopes)}")
    print(f"Elapsed: {perf_counter() - started:.3f}s")


if __name__ == "__main__":
    main()
