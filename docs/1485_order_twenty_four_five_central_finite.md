# Five central vertices and nine tops: a finite incidence exclusion

Research note, 18 September 2026. This completes the five-central-vertex
case at order 24. Its last step is an explicit exact-cover enumeration,
not a SAT or ATP exclusion. The reduction and enumeration are specified
below, but have not yet been formalized in Lean.

The [five-central reduction](1485_order_twenty_four_five_central.md)
leaves degree classes `Z,A,B,T`, of degrees `3,4,6,8`, with sizes
`5,5,5,9`. We show that the central incidence permits at most two
degree-four vertices, contradicting the required five.

## The finite lemma

Let `Z={0,1,2,3,4}` and suppose nine nonempty rectangles
`R_t×C_t` partition `Z×Z`, with the following additional properties:

1. Each side has size at most three.
2. Every point occurs in exactly three predecessor sets `R_t` and
   exactly three successor sets `C_t`.
3. For every pair of rectangles, `|C_t∩R_u|≤1`.

Set `K_tu=|C_t∩R_u|`. An admissible profile is a pair `(P,Q)` of
three-element subsets of the rectangle indices such that

\[
 \{R_t:t\in P\}\text{ partitions }Z,
 \qquad \{C_u:u\in Q\}\text{ partitions }Z,
 \qquad K_{P,Q}\text{ is a permutation matrix}.
 \tag{1}
\]

**Finite lemma.** Every such system has at most two admissible profiles.

## Exhaustive generation by the central pair graph

Define a simple graph `F` on `Z`: a pair is an edge when its two
points occur together in at least one `R_t`. Then every `R_t` is a
clique of `F`. Every `C_u` is an independent set of `F`, since an
edge inside it would contradict condition 3. Conversely this
clique/independent-set condition implies condition 3.

There are ten unordered pairs on `Z`. The checker generates all
`2^10` labeled graphs, quotienting by all 120 permutations of `Z`;
there are 34 representatives. This list is computed directly, not
taken from an external graph catalogue. Simultaneously relabeling
the two coordinates of a rectangle system relabels its pair graph,
so considering these representatives loses no possible system.

For each graph the following finite algorithm enumerates its systems:

1. List every nonempty clique `R` and independent set `C` of size at
   most three. These give all candidate rectangles `R×C`.
2. Select an uncovered cell of the central five-by-five square.
   Branch over every candidate rectangle covering that cell which
   does not overlap a previously chosen rectangle.
3. Keep each row's and column's rectangle-incidence count at most
   three. If the number of remaining rectangles cannot raise a count
   to three, discard the branch.
4. At nine rectangles, retain the choice precisely when all 25 cells
   are covered, all ten incidence counts are three, and the union of
   the predecessor-pair sets is exactly the chosen graph `F`.
5. For each retained system, test all three-element subsets for the
   three conditions in (1), and assert that their number is at most two.

Every desired cover survives these steps: at each chosen uncovered
cell it has exactly one rectangle to select, and the incidence bounds
are necessary. Conversely the terminal tests are precisely the stated
rectangle hypotheses and the definition of the pair graph. Selecting
the cell with the fewest candidates is only a search-order optimization.
No bound on the number of profiles is used to prune the search.

The complete implementation uses only exact integers, finite sets,
and the Python standard library:

```sh
python3 scripts/1485_m5h9_incidence_check.py
```

It is provided in
[1485_m5h9_incidence_check.py](../scripts/1485_m5h9_incidence_check.py).
The run takes about 23 seconds in the research environment. It checks
8,887 rectangle systems: 8,539 have no admissible profile, 332 have one,
and 16 have two. The bound is asserted separately on every system;
the summary counts are not a substitute for that check.

This finite proof is reproducible without a model bank, heuristic
search, SAT certificates, or an assumed spectrum. A purely analytic
replacement and a Lean implementation remain desirable further work.

## Why this excludes the magma

For a top vertex `t`, take `R_t,C_t` to be its central predecessor
and successor sets. Unique goodness between central endpoints says
that their nine rectangles partition `Z×Z`. Central degree three
gives condition 2, and uniqueness of a central good middle between
top endpoints gives condition 3. The established sharp-neighbor
bound gives the side-size bound.

Every degree-four vertex `a` has exactly one sharp degree-six neighbor
and three top neighbors in each direction. This follows from the
central injection in the preceding reduction. Let `P_a,Q_a` be those
top predecessor and successor triples. Each central row meets `P_a`
exactly once, and each central column meets `Q_a` exactly once,
giving the two partition conditions in (1).

For any `t∈P_a`, the three-element fiber `L_t^{-1}(a)` consists of
one sharp degree-six successor of `a` and two of its three top
successors. Thus exactly one path through `a` is bad in each row
of `P_a×Q_a`; the dual count gives exactly one in each column.
Such a path is bad precisely when it has a central good middle:
strict degree descent leaves central degree three as the only
smaller possibility. Therefore `K_{P_a,Q_a}` is a permutation matrix.

Finally, distinct degree-four vertices have distinct ordered profiles.
There are six noncentral endpoint pairs in each admissible profile.
Any degree-four middle at such a pair must be good, since a bad one
would require a central replacement. Two vertices sharing a profile
would thus give two good middles at the same endpoint pair.

The five degree-four vertices require five admissible profiles,
contradicting the finite bound of two. This completes the exclusion.

## Complete enumeration summary

The mask's bit positions, from least significant to most significant,
are the pairs `01,02,03,04,12,13,14,23,24,34`. A representative is
the smallest mask among all relabelings. The diagram counts still
distinguish central labelings fixing that graph; they are not claimed
to be isomorphism-class counts of magmas or rectangle systems.

| Pair-graph mask | Diagrams with 0 / 1 / 2 admissible profiles |
| --- | --- |
| 0 | 0 / 0 / 0 |
| 1 | 0 / 0 / 0 |
| 3 | 0 / 0 / 0 |
| 7 | 0 / 0 / 0 |
| 15 | 0 / 0 / 0 |
| 19 | 729 / 0 / 0 |
| 20 | 2504 / 240 / 0 |
| 21 | 0 / 0 / 0 |
| 23 | 480 / 0 / 0 |
| 28 | 1416 / 8 / 16 |
| 29 | 0 / 0 / 0 |
| 31 | 96 / 0 / 0 |
| 54 | 558 / 16 / 0 |
| 55 | 306 / 0 / 0 |
| 58 | 322 / 6 / 0 |
| 59 | 252 / 12 / 0 |
| 62 | 148 / 4 / 0 |
| 63 | 72 / 0 / 0 |
| 126 | 48 / 0 / 0 |
| 127 | 24 / 0 / 0 |
| 183 | 0 / 0 / 0 |
| 184 | 864 / 0 / 0 |
| 185 | 168 / 16 / 0 |
| 187 | 116 / 0 / 0 |
| 191 | 0 / 0 / 0 |
| 207 | 100 / 0 / 0 |
| 220 | 250 / 0 / 0 |
| 221 | 50 / 30 / 0 |
| 223 | 24 / 0 / 0 |
| 254 | 0 / 0 / 0 |
| 255 | 0 / 0 / 0 |
| 495 | 12 / 0 / 0 |
| 511 | 0 / 0 / 0 |
| 1023 | 0 / 0 / 0 |
