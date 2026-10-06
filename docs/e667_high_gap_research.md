# E667/E883: extended designs lower the common tail to 340

Update, October 5: order 339 is now proved and the E667/E883 tails are 220.
See [the projective-frame construction](e667_order339_20261005.md).
The dated account below records the earlier state.

The new Lean construction proves every order **n ≥ 340** for both E667 and
E883, improving the previous common cutoff of 1228. In particular, all eight
high gaps requested in the research task are now filled. The same constructions
supply 29 new **idempotent E63** orders and improve that stronger tail to **689**.
They do not settle E667 at 12 or 15.

The public declarations are `Spectrum.E667.ExtendedBounds.lower`, `all_large`,
and `cofinite`, and their `E883` counterparts, in
`Spectrum/Equation667883ExtendedBounds.lean`. For idempotent E63, the declarations
are `Spectrum.E63.ExtendedBounds.extra_model`, `model`, and `all_large` in
`Spectrum/Equation63/ExtendedBounds.lean`.

## Remaining cases

E667 has 17 remaining open orders; its separately proved exclusions are 3 and 6:

```
12, 15, 24, 30, 39, 48, 51, 60, 75, 87, 96, 102, 159, 174, 195, 219, 339
```

E883 has 21 remaining open orders; its separately proved exclusions are 3, 6,
and 9:

```
12, 15, 18, 24, 30, 39, 48, 51, 60, 75, 87, 96, 99, 102, 153, 159, 174,
195, 207, 219, 339
```

The added E667 orders are 123, 303, 543, 615, 717, 723, 807, 843, 867, 933,
1203, and 1227. E883 gains all twelve and also 387, 927, and 1017. E883's
existing spectrum transfers apply to its companion laws.

## Two extensions of the existing gluing argument

An idempotent E63 operation satisfies `y*(x*(x*y))=x` and `x*x=x`.
Its two-variable identity survives gluing over a pairwise balanced design:
any two distinct points lie in one block, and all subsequent products used by
the identity stay in that block. This also transfers to E667 and, by the
existing left-division construction, to E883.

The previous seven-group construction used a TD(8,q), retaining seven whole
groups of size q and r points of its last group. This gives order `7q+r` if
idempotent fillings exist at q and r. Two modest extensions were missing:

1. **An arbitrary number of groups.** A TD(k+1,q) gives order `kq+r` if the
   group sizes q,r and block sizes k,k+1 have idempotent fillings. For example,
   `1017 = 31·32+25`, using a field TD(32,32) and the known fillings at
   31,32,25. This is `HasWideTD.idempotent_models` in `ExtendedDesign.lean`.
2. **One shared extra point.** Add a single point ∞ to every retained group.
   The enlarged groups, together with the old transversal blocks, form a
   pairwise balanced design: pairs in one group or containing ∞ are covered
   by an enlarged group, and other pairs are covered by their transversal
   block. Thus a TD(8,q) gives order **`7q+r+1`** from idempotent fillings at
   **q+1,r+1**, together with the usual block fillings 7,8. This is
   `HasTD.pointed_models` in `PointedDesign.lean`.

The shared point is essential: a design may exist at q even when no
idempotent q-point filling is known, but q+1 can have a filling.

## Explicit decompositions

All group and block fillings in this table were already available, apart from
123, which is constructed in its first row.

| New order | Construction | Design source |
|---|---|---|
| 123 | `7·16+10+1` | Field of order 16; fillings 17 and 11 |
| 303 | `7·40+23` | Binary-field difference matrix at 40 |
| 387 | `7·50+37` | V(6,7) quasi-difference matrix at 50 |
| 543 | `7·76+10+1` | Projective-plane construction at 76; fillings 77 and 11 |
| 615 | `5·123` | Direct product |
| 717 | `7·100+16+1` | V(8,11) design at 100; fillings 101 and 17 |
| 723 | `7·100+22+1` | Same design; fillings 101 and 23 |
| 807 | `7·104+78+1` | Product designs at 8 and 13; fillings 105 and 79 |
| 843 | `7·112+58+1` | Product designs at 7 and 16; fillings 113 and 59 |
| 867 | `7·112+82+1` | Same design; fillings 113 and 83 |
| 927 | `7·128+30+1` | Field of order 128; fillings 129 and 31 |
| 933 | `7·128+36+1` | Same design; fillings 129 and 37 |
| 1017 | `31·32+25` | Field TD(32,32); block fillings 31 and 32 |
| 1203 | `7·160+83` | Binary-field difference matrix at 160 |
| 1227 | `7·160+107` | Same design |

An alternative construction of 1203 is `32·37+19`, using a TD(33,37) and
block fillings at 32 and 33.

## The additional designs and their checks

The source of the finite construction data is SageMath's public design
database. The repository stores the parameters, reconstruction scripts, and
Lean certificates; no Sage installation is required to reproduce them.

* **Orders 40 and 160.** Abel's binary-field construction expands a small
  matrix over `Z/5 × GF(2^c)` into seven difference rows. Every difference of
  two rows runs through the group exactly once. Developing by translations
  and adjoining the row-index coordinate yields TD(8,40) and TD(8,160).
  Their Lean interfaces are `TD40.exists_td` and `TD160.exists_td`.
* **Orders 50 and 100.** The vectors
  `V(6,7)=(0,1,3,16,35,26,36)` over `F43` and
  `V(8,11)=(0,1,6,56,22,35,47,23,60)` over `F89` give quasi-difference
  matrices. Multiply by the appropriate roots of unity, rotate the columns,
  and append the zero row. Develop by translations, leaving the missing
  entries fixed, then fill the 7- or 11-point hole with a field design.
  `QuasiDifference.lean` proves this development abstractly. The concrete
  files check short left-inverse certificates for the difference rows, so
  they do not enumerate pairs of developed blocks.
* **Order 76.** Start with cyclic PG(2,9), whose base line is
  `[0,1,3,9,27,81,61,49,56,77]` modulo 91. Remove this line and the five
  oval points `[2,4,5,12,24]`. The remaining pairwise balanced design has
  ten blocks of size 7 and eighty blocks of sizes 8 or 9. Fill the latter
  with field orthogonal arrays after removing their constant rows. For
  each 7-block, use a TD(8,7) with one constant row removed. The designated
  critical points ensure that each point supplies diagonal pairs at most
  once; add the remaining constant rows. This gives 5,776 blocks on eight
  groups of size 76. The stored coordinate data are compressed. Lean checks
  that sorting the ordered-pair images of every pair of columns gives
  exactly `[0,...,76²-1]`. The generic proof in `TableDesign.lean` turns this
  into a transversal design without quadratic comparisons of block pairs.

The finite difference and sorted-image checks use the repository's registered
native checking mechanism. The gluing and development arguments are ordinary
Lean proofs; the other small finite checks and coverage calculations use
`decide +kernel`. There are no new admitted steps. All public bound declarations
pass `spectrum_assert ... complete`.

Local builds, under concurrent research load, took roughly 6–10 seconds each
for the designs at 40,76,160; 14 seconds at 50; 20–27 seconds at 100; and
15 plus 12 seconds for the two final bound modules.

## Reproduction

```
python3 scripts/spectrum_binary_difference_designs.py --check
python3 scripts/spectrum_quasi_difference_designs.py --check
python3 scripts/spectrum_td76.py --check
python3 scripts/spectrum_667_extended_bounds.py --check
lake build equational_theories.Spectrum.Equation667883ExtendedBounds
```

The generator gives 29 new idempotent E63 orders:

```
123, 299, 303, 355, 358, 377, 387, 543, 559, 587, 611, 615, 717, 723, 755,
807, 811, 843, 863, 867, 895, 923, 927, 933, 1017, 1108, 1203, 1207, 1227
```

The idempotent E63 lower bound now leaves 111 possible exceptions, all below
689. They are construction gaps, not nonexistence claims.

## Next obstruction

Order 339 remains at the top of both ordinary spectra. A TD(8,44) would fill
it via `339=7·44+30+1`, with existing fillings at 45 and 31. However, the
Handbook of Combinatorial Designs table recorded in Sage gives only **five**
MOLS at order 44, which supplies TD(7,44), not TD(8,44). Thus this tempting
construction is not currently justified by those bounds. It should not be
silently added to the spectrum.

## Follow-up cyclic-design searches (inconclusive)

A cyclic PBD(v,{5,7,8}) can be specified by a short difference family: the
unordered cyclic distances between points of its base blocks must partition
`1,...,(v-1)/2`. It would supply another idempotent E63 model. The following
block-size multisets satisfy the necessary pair counts:

| v | Base-block sizes |
|---|---|
| 159 | three 5-blocks, one 7-block, one 8-block |
| 195 | two 5-blocks, one 7-block, two 8-blocks |
| 219 | six 5-blocks, one 7-block, one 8-block |
| 339 | twelve 5-blocks, one 7-block, one 8-block; or five 5-blocks, three 7-blocks, two 8-blocks |

Eight independent 180-second annealing runs at 339 and two each at 159,195,219
found no exact difference families. Their best remaining collision counts were
4,2,3,2 respectively (in the order 339,159,195,219). Nine 90-second CP-SAT runs
at 159,195,219 also returned UNKNOWN. Those searches normalized cyclic shifts
within base blocks and considered each possible block size containing the
distance 1.

The saved near-family at 159 repeats distances 46 and 10 and misses distances
5 and 36. Exact clique enumeration rules out replacing any one or two of its
blocks while leaving the others fixed. This is a statement about that
particular near-family, not a nonexistence result for cyclic designs or magmas.

The reproducible tools are `scripts/spectrum_667_cyclic_design_search.cpp`,
`scripts/spectrum_667_cyclic_cp.py`, and `scripts/spectrum_667_cyclic_repair.py`.
Results and the explicitly marked **non-certificate** near-family are in
`data/spectrum/e667_cyclic_design_research.json`. None of these unsuccessful
searches alters the proved bounds above.

## Certificate cleanup audit

The cutoff-340 argument above was already fully formalized. The follow-up
integration audit found one remaining redundant E667 multiplication-table
proof: the nine-element example in `Generated/NoteWitnesses.lean`. Its catalogue
entry now uses `E667.square_model 3` directly. The historical seven-element
entry uses `E63.idem7.hasModel667`, and the singleton uses `Law667.hasModel_one`.
The cached E667 tables at orders 1,7,9 (131 entries altogether) have been removed,
and the witness generator preserves these construction-based replacements.

The compatibility declarations `Pending.cofinite_667` and
`Pending.cofinite_883` now point directly to the cutoff-340 construction rather
than the older cutoff-1228 theorem. All published bounds and lists of unresolved
orders are unchanged. The shared E63 seeds, transversal-design certificates,
and separate nine-element counterexamples used for structural research remain
necessary for their own results and are retained.

Validation after cleanup: all design/bound generators and the full catalogue
regenerator passed `--check`; the targeted build through `Spectrum.Catalogue`
passed. A separate Lean audit marked the exported E667/E883 lower, tail, and
cofiniteness declarations complete, including their compatibility wrappers.
The scoped witness regenerator left the cleaned cache unchanged.
