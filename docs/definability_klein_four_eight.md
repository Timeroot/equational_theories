# Two finite FO separations from the same eight-point action

E167 and E1483 both fail to finitely FO-define E4405. Each has an eight-point
model admitting V4 acting freely on two four-point orbits. The existing
`noprn8h4a_Law4405` theorem excludes every invariant E4405 operation. A
parameter-free definable operation preserves each source automorphism, so
neither source admits such an operation. These are negative results for
finite FO definability and hence for every stronger structural or term mode,
as well as the unrestricted variants.

The shared application of the existing target exclusion is now in
`Definability/KleinFourEight.lean`, theorem
`Magma.KleinFourEight.not_definable`. The two source modules are
`Definability/BookendEight.lean` and `Definability/Central1483Eight.lean`.
The new source-law facts are checked by kernel reduction. E167 adds a small
table and symmetry checks; E1483 reuses the existing `prn8h4aM1485` table and
automorphism lemmas, since that model also satisfies E1483. Thus
no new native computation or certificate is added. The target theorem retains
its existing native-search dependency. The three modules built in 4.8, 3.6,
and 5.2 seconds respectively after the final reuse cleanup.

The new public arrows are:

- `Equation4405_not_definableFromFin_Equation167`;
- `Equation4405_not_definableFrom_Equation167`;
- `Equation4405_not_definableFromFin_Equation1483`;
- `Equation4405_not_definableFrom_Equation1483`.

An E1483 witness was found in 0.071 seconds. Its law was independently checked
on all 512 triples and its automorphisms on all input pairs before the Lean
verification. The Lean proof was then simplified to reuse the earlier
`prn8h4aM1485` source. Both tables and the discovery numbering change are in
`data/definability_1483_4405_separation.json`; the E167 counterpart is in
`data/definability_167_4405_separation.json`. The E167 research note also gives
a direct, general construction explaining that source action.

`scripts/definability_klein_four_eight_probe.py` reproduces the bounded source
searches. Under this particular action, E1486, E3342, E3545, and E4443 were
UNSAT in under 0.3 seconds each. Those are exploratory exclusions, not new
Lean theorems, and say nothing about these laws under other actions.

## The E117 structural follow-up

The eight-point E167 source does **not** obstruct finite FO structurality to
E117. A search found an E117 operation with exactly the same V4 automorphism
group. By the finite bridge, the operations are mutually parameter-free
FO-definable on that specific carrier. No global structural arrow follows.

The same test succeeded for all thirteen selected E167 sources of orders
4, 8, 9, 12, 13, and 16. Their full automorphism groups include C2, C4, V4,
a group of order 48, and affine groups of orders 39, 52, and 72. The search
first enforces invariance under the source group, then excludes extra target
automorphisms until the full groups agree. Each solve had a five-second limit
and each source allowed at most forty exclusions; all selected instances
finished in under a second. Source and target laws were checked directly, and
Pynauty computed the full groups. These are research checks, not Lean proofs.

The source/target pairs are saved in `data/definability_167_117_probe.json`.
Run `scripts/definability_167_117_probe.py` to recheck all pairs and full group
equalities, or add `--search` to repeat the bounded searches. The global
E167-to-E117 FO structural question remains open.

## Check of every catalogue law on the witnesses

All 4694 laws were evaluated on each source. The E167 table satisfies 48 laws;
its previously open source classes toward E4405 were E167, E1682, and E3675.
The latter two exclusions already follow from the new E167 result and the
existing E167-to-E1682/E3675 definability constructions. Both E1483 tables
satisfy the same 35 laws; E1483 was their only previously open source class
toward E4405. Thus the scan found no further independent separation to add.

The complete satisfied-law lists are in
`data/definability_klein_four_eight_scan.json`. Reproduce them with
`scripts/definability_klein_four_eight_scan.py`; its open-arrow comparison uses
the saved audit snapshot, so that list should become empty after integration.
