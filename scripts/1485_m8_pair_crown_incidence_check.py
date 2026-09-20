"""Verify two necessary-incidence examples, NOT E1485 magma models.

No search or third-party solver is used. The incomplete multiplication
table leaves noncentral top products undefined.
"""

from itertools import product

EXAMPLES = (
    (
        (((0,3),(0,1)), ((1,5),(1,2)), ((2,4),(2,3)), ((6,7),(3,4)),
         ((2,4),(0,1)), ((0,3),(2,3)), ((1,4),(4,6)), ((0,2),(5,7)),
         ((1,5),(3,5)), ((0,3),(4,6)), ((2,5),(4,6)), ((4,7),(5,7)),
         ((3,6),(5,7)), ((1,5),(0,7)), ((6,7),(0,1)), ((6,7),(2,6))),
        ((1,8,9,13), (3,12,14,15), (3,4,11,15), (0,5,9,11),
         (1,8,9,13), (3,4,11,15), (0,5,6,7), (2,10,12,14),
         (2,4,10,11), (0,5,6,7), (0,5,6,7), (2,10,12,14),
         (2,10,12,14), (1,8,9,13), (3,4,7,15), (1,6,8,13)),
    ),
    (
        (((0,3),(0,1)), ((1,5),(1,2)), ((2,4),(3,4)), ((6,7),(4,5)),
         ((2,4),(0,1)), ((0,4),(2,6)), ((1,5),(3,4)), ((1,3),(5,7)),
         ((0,3),(3,4)), ((2,3),(2,6)), ((0,4),(5,7)), ((2,5),(5,7)),
         ((1,5),(0,6)), ((6,7),(3,6)), ((6,7),(0,1)), ((6,7),(2,7))),
        ((3,13,14,15), (0,8,9,11), (3,13,14,15), (8,9,11,14),
         (0,8,9,11), (2,4,5,10), (3,13,14,15), (1,6,7,12),
         (0,8,9,11), (2,4,5,10), (1,6,7,12), (1,6,7,12),
         (2,4,5,10), (1,6,10,12), (0,2,5,7), (3,4,13,15)),
    ),
)


def verify(tiles, ordinary):
    assert len(tiles) == len(set(tiles)) == len(ordinary) == 16
    assert all(len(p) == len(set(p)) == len(c) == len(set(c)) == 2
               for p, c in tiles)
    assert {p for p, c in tiles}.isdisjoint({c for p, c in tiles})
    for x, y in product(range(8), repeat=2):
        assert sum(x in p and y in c for p, c in tiles) == 1  # BC=J
    for z, j in product(range(8), range(16)):
        assert sum(j in ordinary[i] for i in range(16) if z in tiles[i][0]) == 1
        assert sum(z in tiles[k][1] for k in ordinary[j]) == 1
    assert all(len(row) == len(set(row)) == 4 for row in ordinary)
    assert all(sum(j in row for row in ordinary) == 4 for j in range(16))

    # Candidate predecessor/successor profiles cover all eight labels.
    for z in range(8):
        assert sum(z in tiles[i][0] for i in range(4)) == 1
        assert sum(z in tiles[i][1] for i in range(4, 8)) == 1
    kernel = [[len(set(c) & set(p)) for p, _ in tiles] for _, c in tiles]
    assert all(entry in (0, 1) for row in kernel for entry in row)
    for i, j in product(range(4), repeat=2):
        assert kernel[i][4+j] == (i != j)

    # Central-assisted unique-return restrictions for the four proposed
    # good pairs (i,4+i). This does not assign or construct their output.
    for i, q in product(range(4), range(16)):
        if kernel[4+i][q] and i in ordinary[q]:
            assert set(ordinary[q]) & set(range(4)) == {i}
        if kernel[q][i] and q in ordinary[4+i]:
            assert {j for j in range(4,8) if q in ordinary[j]} == {4+i}

    adj = [[False] * 24 for _ in range(24)]
    for i, (p, c) in enumerate(tiles):
        for z in p:
            adj[z][8+i] = True
        for z in c:
            adj[8+i][z] = True
        for j in ordinary[i]:
            adj[8+i][8+j] = True
    table = [[None] * 24 for _ in range(24)]
    for x, y in product(range(24), repeat=2):
        mids = [z for z in range(24) if adj[x][z] and adj[z][y]]
        central = [z for z in mids if z < 8]
        if central:
            assert len(central) == 1
            table[x][y] = central[0]
        elif x < 8 or y < 8:
            assert len(mids) == 1
            table[x][y] = mids[0]
    assert sum(value is not None for row in table for value in row) == 448

    def mul(x, y):
        return None if x is None or y is None else table[x][y]

    checked = [0, 0]
    for x, y, z in product(range(24), repeat=3):
        values = (mul(mul(y,x), mul(x,mul(z,y))),
                  mul(mul(mul(y,z),x), mul(x,y)))
        for side, value in enumerate(values):
            if value is not None:
                assert value == x
                checked[side] += 1
    assert checked == [6656, 6656]
    return checked


if __name__ == '__main__':
    for label, example in zip(('four-edge path', 'two two-edge paths'), EXAMPLES):
        checked = verify(*example)
        print(f'{label}: listed incidence/profile/return checks pass; '
              f'{checked} fully determined W/dual instances pass')
    print('These partial incidence systems are not magma models.')
