# Idempotent E667 seed searches — 2026-10-03

We searched for **idempotent** models, including orders already known to have
ordinary E667 models. No new positive seed was found. Consequently the ordinary
E667 tail remains **340**, with the same 17 unresolved orders.

The campaign does exclude idempotent orders **13 and 16** computationally.
This says nothing negative about their ordinary spectra: both orders have
ordinary E667 models. Order 13 is also checked in Lean using a compact
certificate: `Spectrum.E667.not_idempotent_thirteen`. The order-16 argument remains
external, pending formalization.

The [machine-readable report](../data/spectrum/667_idempotent_searches_20261003.json)
records 156 bounded attempts, the seed ranking, solver outcomes, input hashes,
and independently checked positive control tables. The
[log archive](../data/spectrum/667_idempotent_search_logs_20261003.tar.gz)
contains solver logs and first-order inputs. Large reproducible CNFs are not
stored in the repository. The order-13 compact proof is separate from this
research archive.

The order-13 certificate is 1,010,357 compressed bytes. Its module built
successfully in 57 seconds using the compiled certificate-reconstruction
library; no discovery solver runs during an ordinary build.

## Target selection

These gains were calculated by adding one hypothetical idempotent seed and
closing the existing product, singular-product, and transversal-design rules.
They are conditional construction calculations, not existence claims.

| New idempotent seed | Ordinary E667 model already known? | Newly covered E667 orders | Search outcome |
| --- | --- | --- | --- |
| 13 | Yes | 96, 102, 174 | Idempotent subclass excluded |
| 16 | Yes | 219 | Idempotent subclass excluded externally |
| 20 | Yes | 96, 195 | Unresolved |
| 22 | Yes | None immediately; 7 additional idempotent orders | Unresolved |
| 24 | No | 24, 48, 96 | Unresolved |
| 38 | Yes | 339, lowering the tail to 220 | Unresolved |

For example, seeds 20, 16, and 38 would respectively permit
`195 = 7·25 + 20`, `219 = 7·29 + 16`, and `339 = 7·43 + 38`.
The full ranking includes effects on E883 and on the idempotent construction
closure. Restricted cyclic searches also tested 26, 28, 34, 46, 47, 58, and 71.

## Search encodings and controls

Idempotent E667 is exactly idempotent E63. Left division changes the latter
into the shorter cubic law E229,

```
(y * (y * x)) * y = x.
```

We used CaDiCaL with one-hot Latin-table variables, the cubic identity and its
two inverse propagation implications, and idempotence. The unrestricted
encoding uses the already proved first-row chain normalization. Mace4 received
the cubic identity, idempotence, cancellation, and equivalent translation laws.
The initial bounds were 240 seconds per attempt. Those attempts exhausted 13
and timed out at 16, 20, 22, 24, and 38; order 17 was also tried as a control.

Two smaller construction searches complemented the full-table searches:

* The existing cyclic generator now accepts `--idempotent`. Its operation has
  one long automorphism orbit and one or five fixed points. With five fixed
  points it uses a specified labelled affine fixed submodel. Exhaustion therefore
  concerns that construction family, not arbitrary models of the order.
* The new orbit generator identifies SAT variables under a prescribed
  automorphism, allowing several nontrivial orbits. It tested 16 templates at
  orders 16, 17, 20, 22, 24, and 38, generally with 120-second bounds.

The cyclic search reconstructed an idempotent model at **31**. The more general
orbit search reconstructed **17** in 0.017 seconds. Both tables were expanded,
converted back by row inversion, and checked against every original E63 and
E667 instance, as well as idempotence and the Latin conditions. These are
controls for already known seeds, not new spectrum entries. The unrestricted
order-17 SAT attempt timed out despite this known positive answer.

## The order-16 exclusion

Write `L_x(y) = x*y` and `R_x(y) = y*x` for the cubic operation. Finiteness gives
`R_x = L_x^(-2)`. Idempotence and cancellation imply that `L_x` fixes exactly
`x`, and there are no 2-cycles. Thus there are exactly 17 first-row cycle types:
one fixed point followed by a partition of 15 into parts at least three.

1. SAT exhausts all 12 types containing a 3- or 4-cycle. Any point can be
   relabelled as zero, so **every** left translation avoids these cycle lengths.
2. A 3-cycle is detected by `L_x(y) = R_x(y)` for `y ≠ x`; a 4-cycle is detected
   by `L_x²(y) = R_x(y)`. Adding their negations to every row strengthens the
   five remaining cases. SAT then exhausts `5+10`, `6+9`, `7+8`, and `15`, in
   about 12–38 seconds each.
3. Every row must therefore have type `1+5+5+5`, so `L_x^5 = id` for every `x`.
   Mace4 exhausts the following exact-order-16 input in **1.76 seconds**:

   ```
   formulas(assumptions).
   f(f(y,f(y,x)),y)=x.
   f(x,x)=x.
   f(x,f(x,f(x,f(x,f(x,y)))))=y.
   end_of_list.
   ```

The last input uses only the cubic identity, idempotence, and the fifth-power
identity. The case-coverage checks are in the research report. No timeout is
used as an exclusion. Prover9 did not find a general triviality theorem from
these identities; its failed run has no negative mathematical meaning.

## Order 20 and remaining search space

The order-20 row split tested all 39 partitions of 19 into parts at least
three, with 30 seconds per case. **20 cases were exhausted; 19 timed out.**
In particular, only two of the 21 patterns containing a 3-cycle remain:

```
1 + 3 + 3 + 3 + 3 + 7
1 + 3 + 3 + 5 + 8.
```

The October 4 follow-up exhausted both remaining cases, in 52 and 141 seconds.
Thus 3-cycles can now be forbidden globally at order 20, as an **external
solver conclusion**. The 17 surviving row types without 3-cycles each timed
out under the stronger global constraint at 180 seconds; order 20 remains
unresolved in the idempotent subclass. See
[the follow-up report](e667_open_orders_20261004.md) for the coverage audit
and results. At 22, 24, and 38, the earlier unrestricted Mace4 attempts timed
out; their structured searches likewise supplied no new positive model.

## A block-gluing obstruction at 38

There is a short pen-and-paper reason that a direct PBD construction from our
existing smaller idempotent seeds cannot produce 38. This is an obstruction
to that construction method, **not** a nonexistence proof for the magma.

In a nontrivial PBD on 38 points with all blocks of size at least five, every
block has size at most nine: an outside point meets its `k` points in distinct
blocks and consequently has at least `4k` neighbours, so `4k ≤ 37`. Among our
available smaller seeds, only block sizes 5, 7, and 8 remain. At a point, let
`a,b,c` count its incident blocks of these sizes. The equation
`4a+6b+7c=37` forces `c=1` or `c=3`. If there are `m` eight-point blocks and `t`
points incident to three of them, then `8m=38+2t`, so `t=4m−19` and
`5 ≤ m ≤ 14`. Pairs of eight-point blocks meet at most once, giving
`3t ≤ m(m−1)/2`, or `(m−6)(m−19) ≥ 0`. Hence `m=5` or `m=6`.
For `m=6`, all pairs of eight-point blocks meet at triple-incidence points:
each block's five intersections would have to occur in pairs, impossible.
For `m=5`, the unique triple-incidence point belongs to three eight-point
blocks; the other two are disjoint from those and each other. Any additional
block through that point has at most three points, again impossible.

Thus an idempotent seed at 38 would require a construction outside this direct
PBD closure (or a newly discovered smaller seed).

## Reproduction

The main drivers are
[`spectrum_667_idempotent_search.py`](../scripts/spectrum_667_idempotent_search.py),
[`spectrum_667_idempotent_orbits.py`](../scripts/spectrum_667_idempotent_orbits.py),
and [`spectrum_63_cyclic.py`](../scripts/spectrum_63_cyclic.py).

```sh
python3 scripts/spectrum_667_idempotent_search.py --workdir /tmp/e667-idem
python3 scripts/spectrum_667_idempotent_search.py --sat-orders 20 --mace-orders \
  --row-cycles 3 3 5 8 --seconds 30 --workdir /tmp/e667-idem-row
python3 scripts/spectrum_667_idempotent_orbits.py 1 16 --workdir /tmp/e667-idem-control
python3 scripts/spectrum_63_cyclic.py 30 1 --idempotent --seconds 90 \
  --output /tmp/e667-idem-cyclic-control
python3 scripts/spectrum_667_idempotent_thirteen.py
```

The row partitions come from `parts(n-1)` in
`spectrum_667_idempotent_fifteen.py`. The `--no-three-four` switch is a
**restriction**, usable for a full exclusion only after the separate
order-specific short-cycle cases have been exhausted.
