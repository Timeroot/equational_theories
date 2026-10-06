#!/usr/bin/env python3
"""Check explicit E667 constructions from binary block data and S3.

Research witnesses; no output from this script is treated as a Lean proof.
"""
import argparse
import itertools
import json
from pathlib import Path


def properties(q):
    n = len(q)
    assert all(q[y][q[x][q[q[x][x]][y]]] == x for x in range(n) for y in range(n))
    assert all(sorted(row) == list(range(n)) for row in q)
    assert all(sorted(q[x][y] for x in range(n)) == list(range(n)) for y in range(n))
    comm = next(((x,y) for x in range(n) for y in range(n) if q[x][y] != q[y][x]),None)
    medial = next(((x,y,z,w) for x in range(n) for y in range(n)
                   for z in range(n) for w in range(n)
                   if q[q[x][y]][q[z][w]] != q[q[x][z]][q[y][w]]),None)
    d = [q[x][x] for x in range(n)]
    nonhom = next(((x,y) for x in range(n) for y in range(n)
                   if d[q[x][y]] != q[d[x]][d[y]]),None)
    return dict(order=n,verified_original_law=True,diagonal=d,
                idempotents=[x for x in range(n) if d[x] == x],
                commutative=comm is None,noncommuting_pair=comm,
                medial=medial is None,medial_failure=medial,
                square_hom=nonhom is None,nonhomomorphic_pair=nonhom)


def binary(v):
    return [[2*((3*(i+j)) % 5)+(a ^ b ^ v[i] ^ v[(2*j-i) % 5])
             for j in range(5) for b in range(2)] for i in range(5) for a in range(2)]


def s3_mendelsohn():
    es = list(itertools.permutations(range(3)))
    index = {g:i for i,g in enumerate(es)}
    g = [[index[tuple(x[y[i]] for i in range(3))] for y in es] for x in es]
    inv = [row.index(0) for row in g]
    # 0 is the common point; 1+6*c+a is a group element in color c.
    def op(x,y):
        if x == y:
            return x
        if x == 0 or y == 0 or (x-1)//6 == (y-1)//6:
            color = (x-1)//6 if x else (y-1)//6
            a, b = (x-1)%6+1 if x else 0, (y-1)%6+1 if y else 0
            z = (5*a+3*b) % 7
            return 0 if z == 0 else 1+6*color+z-1
        cx,a = divmod(x-1,6)
        cy,b = divmod(y-1,6)
        if (cx,cy) == (0,1):
            color,z = 2,g[a][b]
        elif (cx,cy) == (1,2):
            color,z = 0,g[b][inv[a]]
        elif (cx,cy) == (2,0):
            color,z = 1,g[inv[b]][a]
        elif (cx,cy) == (1,0):
            color,z = 2,g[a][b]
        elif (cx,cy) == (0,2):
            color,z = 1,g[b][inv[a]]
        elif (cx,cy) == (2,1):
            color,z = 0,g[inv[b]][a]
        else:
            raise AssertionError((cx,cy))
        return 1+6*color+z
    m = [[op(x,y) for y in range(19)] for x in range(19)]
    assert all(m[x][x] == x for x in range(19))
    assert all(m[y][m[x][y]] == x for x in range(19) for y in range(19))
    # The new element 19 is a loop unit and the value of every square.
    q = [[y if x == 19 else x if y == 19 else 19 if x == y else m[x][y]
          for y in range(20)] for x in range(20)]
    return dict(group_elements=es,group_table=g,mendelsohn_table=m,table=q,**properties(q))


def existing_counterexample_iso():
    root = Path(__file__).resolve().parents[1]
    old = json.loads((root/'data/spectrum/667_square_retraction_counterexample.json').read_text())
    q = [old['table'][10*i:10*i+10] for i in range(10)]
    fixed = [i for i in range(10) if q[i][i] == i]
    for labels in itertools.permutations(fixed):
        e = []
        for i in labels:
            e.extend([i,next(x for x in range(10) if x != i and q[x][x] == i)])
        ei = {x:i for i,x in enumerate(e)}
        trans = [[ei[q[e[x]][e[y]]] for y in range(10)] for x in range(10)]
        if any(trans[2*i][2*j]//2 != (3*(i+j)) % 5 for i in range(5) for j in range(5)):
            continue
        v = [0]*5
        for j in range(5):
            v[2*j % 5] = trans[0][2*j] % 2
        if trans == binary(v):
            return dict(binary_function=v,explicit_to_saved_labels=e)
    raise AssertionError('Saved model is not in the proposed family')


def nonabelian_difference_design():
    # (a,b)(c,d)=(a+2^b*c,b+d) in C7 semidirect C3, encoded a+7*b.
    g = [[((x % 7)+pow(2,x//7,7)*(y % 7)) % 7 + 7*((x//7+y//7) % 3)
          for y in range(21)] for x in range(21)]
    inv = [row.index(0) for row in g]
    h = [0,3,12,20,17,10,2,16,11,14,4,9,19,1,8,7,18,5,15,6,13]
    q = [[g[x][h[g[inv[x]][y]]] for y in range(21)] for x in range(21)]
    base = properties(q)
    assert base['commutative'] and len(base['idempotents']) == 21 and not base['medial']
    block = [0,1,3,20,13]
    labels = [0,1,3,4,2]
    for i,x in enumerate(block):
        for j,y in enumerate(block):
            assert labels[block.index(q[x][y])] == 3*(labels[i]+labels[j]) % 5
    blocks = {tuple(sorted(g[a][x] for x in block)) for a in range(21)}
    from collections import Counter
    pairs = Counter(pair for bs in blocks for pair in itertools.combinations(bs,2))
    assert len(blocks) == 21 and len(pairs) == 210 and set(pairs.values()) == {1}
    # Change only this block's binary data; every other block has zero data.
    coordinates = dict(zip(block,labels))
    v = [1,0,0,0,0]
    def c(i,j):
        if i not in coordinates or j not in coordinates:
            return 0
        x,y = coordinates[i],coordinates[j]
        return v[x] ^ v[(2*y-x) % 5]
    lift = [[2*q[i][j]+(a ^ b ^ c(i,j)) for j in range(21) for b in range(2)]
            for i in range(21) for a in range(2)]
    return dict(group='C7 semidirect C3, action a -> 2a',profile=h,
                base_block=block,base_block_F5_labels=labels,
                base_properties=base,design_blocks=len(blocks),
                changed_block_binary_function=v,lift_properties=properties(lift))


def binary_classification():
    from spectrum_667_structure import rank
    equations = []
    for i in range(5):
        for j in range(5):
            t = 3*(i+j) % 5
            u = 3*(i+t) % 5
            row = 0
            for a,b in [(i,i),(i,j),(i,t),(j,u)]:
                row ^= 1 << (5*a+b)
            equations.append(row)
    equations += [1 << (6*i) for i in range(5)]
    assert rank(equations) == 21
    automorphisms = []
    for weight in [0,1,2]:
        q = binary([int(i < weight) for i in range(5)])
        aut = []
        for a in range(1,5):
            for b in range(5):
                e = [2*((a*i+b) % 5)+u for i in range(5) for u in range(2)]
                if all(e[q[x][y]] == q[e[x]][e[y]] for x in range(10) for y in range(10)):
                    aut.append([a,b])
        automorphisms.append(dict(weight=weight,affine_automorphisms=aut))
    return dict(normalized_variables=25,constraint_rank=21,dimension=4,
                isomorphism_class_representative_weights=[0,1,2],
                lean_classification='Spectrum.E667.BinaryFive.classify_quotient',
                lean_distinctness='Spectrum.E667.BinaryFive.representatives_distinct',
                automorphism_counts_status='proved in Lean',
                lean_automorphism_counts='Spectrum.E667.BinaryFive.automorphism_card',
                automorphisms=automorphisms)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    args = p.parse_args()
    examples = []
    for weight in [1,2]:
        v = [int(i < weight) for i in range(5)]
        q = binary(v)
        examples.append(dict(binary_function=v,table=q,**properties(q)))
    for bits in itertools.product(range(2),repeat=5):
        props = properties(binary(bits))
        assert len(props['idempotents']) == 5
        assert props['commutative'] == (len(set(bits)) == 1)
        assert props['medial'] == (len(set(bits)) == 1)
        assert props['square_hom'] == (len(set(bits)) == 1)
    out = dict(status='RESEARCH_WITNESSES_INDEPENDENTLY_CHECKED',
               binary_five_point_examples=examples,
               binary_family_lean_theorem='Spectrum.E667.BinaryFive.law',
               lean_results={
                   'binary_extensions': 'Spectrum.E667.BinaryExtensions.every_fiber_extension',
                   'binary_quotient_coordinates': 'Spectrum.E667.BinaryExtensions.quotient_coordinates',
                   'design_construction': 'Spectrum.E667.BinaryDesign.law',
                   'design_completeness': 'Spectrum.E667.BinaryDesign.complete',
                   'design_parameter_count': 'Spectrum.E667.BinaryDesign.normalized_count',
                   'all_binary_extension_count': 'Spectrum.E667.BinaryDesign.all_extension_count',
                   'commutative_binary_count': 'Spectrum.E667.BinaryDesign.commutative_count',
                   'commutative_binary_classification': 'Spectrum.E667.BinaryDesign.commutative_isomorphism',
                   'binary_design_mediality': 'Spectrum.E667.BinaryDesign.medial_iff',
                   'latin_directed_triangles': 'Spectrum.E667.LatinTriangles.law',
                   'frobenius_forty_two': 'Spectrum.E667.Frobenius21.nonlinear_double_cover',
                   'commutative_design': 'Spectrum.E667.CommutativeDesign.cover',
                   'commutative_design_orders': 'Spectrum.E667.CommutativeDesign.card_mod_twenty',
                   'group_directed_triangles': 'Spectrum.E667.GroupMendelsohn.law',
                   's3_twenty_noncommutative': 'Spectrum.E667.GroupMendelsohn.s3_noncommutative',
                   'frobenius_twenty_one': 'Spectrum.E667.Frobenius21.law',
                   'affine_group_obstruction': 'Spectrum.E667.GroupConstructions.affine_forces_commutative',
                   'regular_group_latin_criterion': 'Spectrum.E667.GroupConstructions.regular_latin_iff',
                   'affine_idempotent': 'Spectrum.E667.AffineStructure.affine_has_idempotent',
                   'affine_splitting': 'Spectrum.E667.AffineStructure.unique_splitting',
                   'affine_three_adic_obstruction': 'Spectrum.E667.AffineStructure.three_dvd_implies_nine_dvd',
                   'affine_prime_obstruction': 'Spectrum.E667.AffineStructure.prime_square_dvd_of_no_root',
                   'cyclic_affine_criterion': 'Spectrum.E667.AffineStructure.cyclic_affine_iff',
                   'universal_affine_squares': 'Spectrum.E667.AffineStructure.squareMatrix_law',
                   'universal_affine_cubes': 'Spectrum.E667.AffineStructure.cubeMatrix_law',
                   'infinite_affine_quasigroups': 'Spectrum.E667.AffineStructure.affine_latin',
                   'frobenius_extension_counts': 'Spectrum.E667.Frobenius21.binary_extension_counts',
               },
               binary_classification=binary_classification(),
               existing_counterexample=existing_counterexample_iso(),
               nonabelian_group_design=s3_mendelsohn(),
               nonabelian_difference_design=nonabelian_difference_design())
    text = json.dumps(out,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text,end='')


if __name__ == '__main__':
    main()
