# Order twenty-four with four central vertices: an explicit finite incidence proof

Research note, 18 September 2026. This excludes the four-central-vertex
case at order 24 and minimum translation degree three. The last step
is a small exhaustive combinatorial calculation, fully specified below
and implemented using only the Python standard library. It is not a SAT
or ATP result, and it has not yet been checked in Lean. The proof should
therefore be distinguished from the purely analytic exclusions in the
neighboring notes.

**Theorem.** No E1485 magma of order 24 and minimum translation degree
three has exactly four central vertices.

The [small-central reduction](1485_order_twenty_four_small_central.md)
already excludes top-class sizes eight and ten. In the remaining case,
there are nine top vertices. Their central predecessor/successor types
are one `(2,2)`, two `(1,2)`, two `(2,1)`, and four `(1,1)`.
That note's final section analytically excludes degree-four vertices
with sharp degree two. Every degree-four vertex consequently has sharp
degree one and three top neighbors in either direction; their number
is six or seven.

We prove that there can be at most four such vertices by counting their
possible top profiles.

## A finite central-rectangle lemma

Let the central set be `Z={0,1,2,3}`. For each of the nine top vertices
`t`, write `R_t,C_t⊆Z` for its central predecessor and successor sets.
They satisfy:

1. The rectangles `R_t×C_t` partition `Z×Z`.
2. Each central element belongs to exactly three `R_t` and exactly
   three `C_t`.
3. `|C_t∩R_u|≤1` for any two top vertices `t,u`.
4. Their size pairs have the multiplicities listed above.

The first three statements respectively express existence and uniqueness
of good middles between central endpoints, central translation degree
three, and uniqueness of a central middle between top endpoints.
Put `K_tu=|C_t∩R_u|`, a zero-one matrix by condition 3.

Call a pair `(P,Q)` of three-element subsets of the top set admissible
when

\[
 \{R_t:t\in P\}\text{ partitions }Z,
 \qquad \{C_u:u\in Q\}\text{ partitions }Z,
 \qquad K_{P,Q}\text{ is a permutation matrix}. \tag{1}
\]

**Finite lemma.** Every rectangle system satisfying conditions 1--4
has at most four admissible pairs.

Here is an exhaustive generation and checking procedure for the lemma.
It also explains why the calculation has only `2·6⁴=2592` initial
placements, not a search over magma tables.

* Label the unique two-by-two rectangle `H`. Relabel `Z` so that
  `R_H={0,1}`. Condition 3 excludes `C_H=R_H`. Up to permutations
  preserving `R_H`, the two possibilities are `C_H={2,3}` and
  `C_H={0,2}`.
* Each central row belongs to one rectangle with successor size two,
  since its three positive successor sizes sum to four. Thus the
  singleton predecessor sets of the two one-by-two rectangles are
  exactly `{2}` and `{3}`. Dually, the singleton successor sets of
  the two two-by-one rectangles are the two elements outside `C_H`.
* Choose the remaining side of each of those four rectangles. Each
  side is a two-element subset of `Z`, giving six choices apiece.
* Discard placements where these five rectangles overlap. They cover
  twelve cells. The four remaining cells must be the four singleton
  rectangles, so there is no further choice.
* Check conditions 2 and 3. Exactly 285 normalized labeled diagrams
  remain. For each, examine the `binom(9,3)` possible sets on each
  side and check the three explicit conditions in (1). The maximum
  number of admissible pairs is four.

Every permitted rectangle system occurs in this list: each normalization
step is a relabeling, and every unspecified side was allowed all six
possibilities. Conversely all retained systems satisfy conditions 1--4.
The profile test in (1) involves only intersections of subsets of a
four-element set.

The complete executable check is
[1485_m4h9_incidence_check.py](../scripts/1485_m4h9_incidence_check.py).
In particular it checks the bound on **every one of the 285 raw
diagrams before canonicalization**. The subsequent relabeling and
duality quotient is only a compact presentation of the inventory,
not a dependency of that bound.

```sh
python3 scripts/1485_m4h9_incidence_check.py --all
```

The check takes approximately 0.4 seconds in the research environment.
It uses no external packages, downloaded tables, heuristic solver,
floating-point arithmetic, or proposed E1485 spectrum conclusions.
An independent Lean `decide` implementation of this finite lemma remains
future work.

## Why the lemma bounds degree-four vertices

Let `a` be a degree-four vertex, with top predecessor and successor
sets `P_a,Q_a`. Each has size three. Every central row has exactly
one good middle leading to `a`, and every central column has exactly
one good middle coming from `a`. This gives the first two partition
conditions in (1).

For `t∈P_a`, the three-element fiber `L_t^{-1}(a)` contains the
unique sharp degree-six successor of `a`, and exactly two of its
three top successors. Exactly one of the three top paths through
`a` is therefore bad. A bad degree-four middle has central good
replacement, by strict degree descent; conversely a central middle
makes the path through `a` bad by uniqueness. The dual count applies
to each member of `Q_a`. Thus `K_{P_a,Q_a}` is a permutation matrix,
so the pair is admissible.

Two distinct degree-four vertices cannot have the same admissible pair.
Of the nine endpoint pairs in `P_a×Q_a`, exactly three have central
middles. At any of the other six pairs, a degree-four middle cannot
be bad, since its strictly smaller replacement would have to be central.
Two such middles would therefore contradict uniqueness of the good path.

The finite lemma now gives at most four degree-four vertices, contradicting
the analytically established lower bound of six. This proves the theorem.

## Complete canonical inventory

The 285 diagrams have 88 representatives under simultaneous relabeling
of the four central vertices and transposition. Top vertices of the
same type are unlabeled in this quotient. Of the representatives,
69 have no admissible pair, six have one, ten have two, and three have
four.

In the table, four slash-separated strings are the rows of the central
four-by-four rectangle table. `H` labels the two-by-two rectangle;
`A,B` label the one-by-two rectangles; `C,D` label the two-by-one
rectangles; and `0,1,2,3` label the singleton rectangles. These table
letters name top vertices, not the degree classes used elsewhere.
For example `03D→02H` means the admissible pair
`P={0,3,D}`, `Q={0,2,H}`. All 88 representatives are included, including
the zero-profile cases.

| Central rectangle table | Admissible profile pairs |
| --- | --- |
| `01AA/CDHH/CDHH/23BB` | none |
| `01AA/CDHH/CDHH/2B3B` | none |
| `01AA/CDHH/CDHH/BB23` | none |
| `01AA/CDHH/CDHH/B2B3` | `03D→02H; 03D→2AC; 13C→02H; 13C→2AC` |
| `01AA/CDHH/CDHH/B23B` | none |
| `01AA/CDHH/CDBB/23HH` | none |
| `01AA/CHDH/CHDH/2B3B` | none |
| `01AA/CHDH/CHDH/BB23` | `03D→02H; 13C→02H` |
| `01AA/CHDH/CHDH/B2B3` | `03D→2AC; 13C→2AC` |
| `01AA/CHDH/CHDH/B23B` | none |
| `01AA/CDHH/C2HH/BDB3` | none |
| `01AA/CDHH/C2HH/BD3B` | none |
| `01AA/HHCD/HHCD/23BB` | none |
| `01AA/HHCD/HHCD/2B3B` | `03D→0BC; 12D→0BC` |
| `01AA/HHCD/HHCD/B23B` | `02D→1BC; 03D→1BC` |
| `01AA/HHCD/HHC2/BB3D` | none |
| `01AA/HHCD/HHC2/B3BD` | none |
| `01AA/HHDC/HH2C/BBD3` | none |
| `01AA/HHDC/HH2C/B3DB` | none |
| `01AA/HHCD/HH23/BBCD` | none |
| `01AA/HCHD/HCHD/23BB` | `03D→0BC; 03D→2AC; 12D→0BC; 12D→2AC` |
| `01AA/HCHD/HCHD/2B3B` | `03D→2AC; 12D→2AC` |
| `01AA/HCHD/HCHD/B23B` | none |
| `01AA/HCHD/HCH2/BB3D` | none |
| `01AA/HCHD/HCH2/B3BD` | none |
| `01AA/HDHC/H2HC/3DBB` | none |
| `01AA/HDHC/H2HC/BDB3` | none |
| `01AA/HDHC/H2HC/BD3B` | none |
| `01AA/HCHD/H2H3/BCBD` | none |
| `01AA/HCDH/HCDH/23BB` | none |
| `01AA/HCDH/HCDH/2B3B` | none |
| `01AA/HCDH/HCDH/BB23` | `03C→12H; 03D→12H` |
| `01AA/HCDH/HCDH/B2B3` | none |
| `01AA/HCDH/HCDH/B23B` | none |
| `01AA/HCDH/HC2H/BBD3` | none |
| `01AA/HCDH/HC2H/B3DB` | none |
| `01AA/HDCH/H2CH/3DBB` | none |
| `01AA/HDCH/H2CH/BDB3` | none |
| `01AA/HDCH/H2CH/BD3B` | none |
| `01AA/HCDH/H23H/BCDB` | none |
| `01HH/CDHH/CDAA/B23B` | none |
| `01HH/CDHH/C2AA/BDB3` | none |
| `01HH/CDHH/C2AA/BD3B` | `13C→0AD` |
| `01HH/CDAA/CDHH/B23B` | none |
| `01HH/CDAA/C2HH/BD3B` | `13C→02A` |
| `0AAC/H1HC/BD2B/HDH3` | none |
| `0AAC/BB12/DHH3/DHHC` | none |
| `0AAC/BB12/HHD3/HHDC` | none |
| `0AAC/BB12/HDH3/HDHC` | none |
| `0AAC/BDB1/H2H3/HDHC` | none |
| `AA01/2BB3/CHHD/CHHD` | none |
| `AA01/2BB3/CHDH/CHDH` | none |
| `AA01/2BB3/HHCD/HHCD` | none |
| `AA01/2BB3/HCHD/HCHD` | none |
| `AA01/2BB3/HCDH/HCDH` | `02C→3AD; 12C→3AD` |
| `AA01/2BBC/DHH3/DHHC` | none |
| `AA01/2BBC/HHD3/HHDC` | none |
| `AA01/2BBC/HDH3/HDHC` | none |
| `AA01/2H3H/CHDH/CBDB` | none |
| `AA01/2HCH/DHCH/DB3B` | none |
| `AA01/BB23/CHHD/CHHD` | none |
| `AA01/BB23/HHCD/HHCD` | none |
| `AA01/BB2C/DHH3/DHHC` | none |
| `AA01/BB2C/HDH3/HDHC` | none |
| `AA01/BBCD/HHC2/HH3D` | none |
| `AA01/BCB2/HCHD/H3HD` | none |
| `AA01/BCB2/HCDH/H3DH` | none |
| `AA01/BCB2/H3HD/HCHD` | none |
| `AA01/BCB2/H3DH/HCDH` | none |
| `AA01/CBB2/3HHD/CHHD` | none |
| `AA01/CBBD/2HH3/CHHD` | none |
| `AA01/CH2H/CHDH/3BDB` | none |
| `AA01/CH2H/CHDH/B3DB` | none |
| `AA01/HC2H/HCDH/3BDB` | none |
| `AA01/HC2H/HCDH/B3DB` | none |
| `AA01/CDHH/CDHH/23BB` | none |
| `AA01/CDHH/CDHH/2B3B` | `13C→0BC; 12D→0BC` |
| `AA01/CDHH/CDBB/23HH` | none |
| `AA01/CHDH/CHDH/23BB` | `13C→02H; 12D→02H` |
| `AA01/CHDH/CHDH/2B3B` | `13C→0BC; 13C→02H; 12D→0BC; 12D→02H` |
| `AA01/CDHH/C2HH/3DBB` | none |
| `AA01/CDHH/C2HH/BD3B` | `13C→02B` |
| `AA01/CDHH/C2BB/3DHH` | none |
| `AA01/HDHC/H2HC/3DBB` | `03C→1DH` |
| `AA01/HDHC/H2HC/BD3B` | `3AC→02B` |
| `AA01/HCDH/HCDH/23BB` | `12C→03H; 12D→03H` |
| `AA01/HDCH/H2CH/3DBB` | `13C→0DH` |
| `AA0C/HDH1/2DBB/H3HC` | none |
