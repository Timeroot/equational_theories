#!/usr/bin/env python3
"""Small integer audit of nine-central three-profile constraints.

These are central-type counts, NOT magma models. Complete enumeration
uses the two nonnegative slack equations, not a heuristic search.
"""


def moment_tables(h):
    slack = 63 - 3 * h
    for n13 in range(slack // 4 + 1):
        for n31 in range(slack // 4 + 1):
            for n22 in range(slack + 1):
                a = slack - 4 * n13 - n22
                b = slack - 4 * n31 - n22
                if min(a, b) < 0 or a % 2 or b % 2:
                    continue
                for n12 in range(a // 2 + 1):
                    n23 = a // 2 - n12
                    for n21 in range(b // 2 + 1):
                        n32 = b // 2 - n21
                        twice_n33 = 36 - h - n21 - n22 - n23 - 2*n31 - 2*n32
                        if twice_n33 < 0 or twice_n33 % 2:
                            continue
                        n33 = twice_n33 // 2
                        n11 = h - sum((n12,n13,n21,n22,n23,n31,n32,n33))
                        if n11 < 0:
                            continue
                        table = (n11,n12,n13,n21,n22,n23,n31,n32,n33)
                        # Check all moments directly: no reliance on redundant equations.
                        if sum((i+1)*table[3*i+j] for i in range(3) for j in range(3)) != 36:
                            continue
                        if sum((j+1)*table[3*i+j] for i in range(3) for j in range(3)) != 36:
                            continue
                        if sum((i+1)*(j+1)*table[3*i+j] for i in range(3) for j in range(3)) != 81:
                            continue
                        yield table


def size_two_coverage(table):
    return (sum((i+1)*table[3*i+1] for i in range(3)) >= 9 and
            sum((j+1)*table[3+j] for j in range(3)) >= 9)


def profile_count_filter(table):
    """Necessary conditions from the complement tilings, not completeness."""
    p3 = sum(table[6:9])
    c3 = sum(table[3*i+2] for i in range(3))
    if p3 < 3 or c3 < 3 or p3 > 6 or c3 > 6:
        return False
    # A central row with two P-triple tops but no paired C-triple or
    # C-singleton cannot contain any other C-singleton: its four sizes
    # would sum at most eight. The exceptional set has size18-3*p3.
    if table[0] + 2*table[3] > 18 - 3*p3 + 3*table[8]:
        return False
    if table[0] + 2*table[1] > 18 - 3*c3 + 3*table[8]:
        return False
    # The maximal-index opposite blocks cover Z. Their central pairs
    # number at least L+R-9, leaving room for the six good pairs of
    # at least one degree-five/three-top-profile vertex.
    left_weight = table[6] + 2*table[7] + 3*table[8]
    right_weight = table[2] + 2*table[5] + 3*table[8]
    if p3*c3 - left_weight - right_weight + 9 < 6:
        return False
    # The global C-triple/P-triple matrix has at most this many zeros.
    max_zeros = (6 - p3) * (6 - c3)
    u_c3 = max(0, 3 - (p3 - table[8]))
    v_p3 = max(0, 3 - (c3 - table[8]))
    needed_zeros = u_c3 * v_p3 - min(u_c3, v_p3)
    if needed_zeros > max_zeros:
        return False
    # A common top lies in both source partitions: its row meets every
    # P-triple in V, and its column meets every C-triple in U. Thus a
    # common top forces exactly one selected triple of each kind.
    possible_overlap = False
    for u in range(u_c3, min(3, table[8]) + 1):
        for v in range(v_p3, min(3, table[8]) + 1):
            if u*v - min(u,v) > max_zeros:
                continue
            for overlap in range(max(0,u+v-table[8]), min(u,v,1)+1):
                if overlap == 0 or u == v == 1:
                    possible_overlap = True
    if not possible_overlap:
        return False
    return True


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: the exact finite case assertions are required.")
    assert set(moment_tables(20)) == {
        (10,1,0,1,1,0,0,0,7), (11,0,0,0,1,1,0,1,6)}
    h19 = {table for table in moment_tables(19) if size_two_coverage(table)}
    assert h19 == {
        (8,0,0,0,4,1,0,1,5),
        (9,0,0,0,0,3,0,3,4),
        (7,1,0,1,4,0,0,0,6)}
    assert not any(profile_count_filter(table) for table in h19)
    assert not list(moment_tables(21))
    for h in range(15,22):
        moments = list(moment_tables(h))
        coverage = [table for table in moments if size_two_coverage(table)]
        profiles = [table for table in coverage if profile_count_filter(table)]
        print(f"h={h}: moments={len(moments)}, coverage={len(coverage)}, "
              f"profile-count filter={len(profiles)}")
        if h == 18:
            for table in profiles:
                print("  surviving h=18 count table:", table)
    print("Exact h=19/20 boundary tables VERIFIED; h=15 needs the analytic disjoint-tiling proof.")


if __name__ == "__main__":
    main()
