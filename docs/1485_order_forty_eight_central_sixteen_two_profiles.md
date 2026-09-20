# Sixteen tops with two small profiles: necessary block restrictions

Independently audited analytic necessary conditions, 20 September
2026. They do **not** exclude the whole two-profile configuration.
No finite enumeration or SAT premise is used.

Assume order forty, minimum degree four, eight central elements,
sixteen tops, ten degree-five elements, and exactly two three-profile
elements. For a top use central block sizes `P,C`, degree-five
incidences `α,β`, and three-profile incidences `γ,δ`.
Let `p,c` count triple blocks in the two directions, and let `n_ij`
count block types. Then

\[
 \boxed{p,c\in\{3,4\},\quad(p,c)\ne(3,3),\quad
        n_{22}\in\{0,2,4\},\quad n_{22}\le4n_{11}.}     \tag{1}
\]

In addition every type `12` has `α=2`, and every type `21`
has `β=2`. If `n22=2`, then `p=c=4,n11=1,n33=0`.
If `n22=0`, then `p=c=4` and the only types are four each of
`12,21,23,32`.

## 1. A singleton-double top cannot have just one degree-five successor

Each central row has four `C` blocks summing to eight, `α` sum
ten, and `γ` sum two. The residual top-input count is

\[
                         R=16-4C-3\alpha+\gamma\ge0.   \tag{2}
\]

In particular, `C=2,α=3` forces `γ≥1`. At `P=1` one has
`γ=0`, so (2) also excludes `P=1,C=2,α=3`.

Suppose a `12` top had `α=1`. Its central row cannot have
pattern `3221`: even the largest other values give
`1+3+4+1=9<10`. It must be `2222`, with the three other
tops all having `α=3`. They contribute at least three to its
`γ` sum, again impossible. The existing incidence interval is
`1≤α≤3` at `C=2`, so every `12` top has `α=2`.
The dual proof gives `β=2` at every `21` top.

## 2. At least three triple blocks are needed in each direction

The one-hole theorem gives `2≤p,c≤4`. Put `v=7−2C−α`.
The central-row equation gives `0≤v≤2`, while the moments give

\[
 \sum v=10,\quad\sum Pv=16,\quad\sum(P-1)v=6.
\]

If `J=Σ_(P=3)v`, then `Σ_(P=1)v=4+J`. Suppose `p=2`.
There are only two singleton predecessor blocks, so the last identity
forces `J=0` and `v=2` at both singleton-predecessor tops.

Both three-profiles use the same two maximal predecessor blocks,
so those two tops have `γ=2`. They cannot have `C=1`, where
`v≥1`, or `C=3`, where `α≤1`; hence both have type `32`.
Their successor profiles are disjoint by the shared-two matching
argument, requiring four triple successor blocks. Thus `c=4`.

At a singleton predecessor with `v=2`, type `13` is impossible
since `v≤1` there. Since there are also no `31` or `33` tops,
the mixed moment `n11+n33=n13+n31` excludes `11` as well.
Both singleton-predecessor tops must therefore have type `12`
and `α=1`, contrary to §1. This excludes `p=2`; duality excludes
`c=2`.

## 3. There cannot be six or eight double-double blocks

Use the local slack `D` and baseline table `(α₀,β₀)` from
the [three-profile proof](1485_order_forty_eight_central_three_three_profiles.md#1-there-are-only-three-possible-numbers-of-double-double-blocks).
Their pointwise comparisons are `α−α₀≤D,β−β₀≤D`. Here

\[
 \sum D=8-n_{22},\qquad
 n_{22}=16-2(p+c)+2(n_{13}+n_{31}).                  \tag{3}
\]

Thus `n22` is even and at most eight. Put `w=n11,z=n33`.
The central moments give

\[
 \sum\alpha_0=\sum\beta_0=32+w-z+n_{22},
 \qquad 3w+z\le p+c\le8.                           \tag{4}
\]

For `n22=8`, all slacks vanish. As in the cited three-profile proof,
`31` tops cannot precede a three-profile and `13` tops cannot
succeed one. The two pools of eligible maximal blocks have total

\[
 (p-n_{31})+(c-n_{13})=(16-n_{22})/2=4.
\]

Two distinct three-profiles require pool total at least six: each
pool has at least two members, and a pool of size two forces the
other pool to contain two disjoint pairs. Contradiction.

Suppose `n22=6`, so `ΣD=2`. Every `22` top with `α=3`
has `γ≥1` by (2). The two three-profiles each have just one
size-two predecessor block, so `Σ_(P=2)γ=2`. At most two
of the six `22` tops have `α=3`. Their total loss from their
baseline value three is therefore at least four. The same holds
dually for `β`. By (4), the actual incidence sum 38 gives

\[
 38\le(38+w-z)+2-4,
 \qquad w-z\ge2.
\]

Together with `3w+z≤8`, this forces `w=2,z=0`. Equation
(3) now gives `p+c=7`. All the preceding inequalities are
equalities. Hence every non-`22` top satisfies both
`α−α₀=D` and `β−β₀=D`. The baseline table shows that
positive slack is possible only at `12:(2,4)` or `21:(4,2)`,
each with slack one. But

\[
 n_{12}+n_{21}=(p+c)-3w-z=1,
\]

so these types cannot carry total slack two. This contradiction
excludes `n22=6` and proves `n22∈{0,2,4}`.

## 4. The local singleton-double restriction improves the moments

By §1, every `12` or `21` top has slack one. Thus

\[
 n_{12}+n_{21}\le\sum D=8-n_{22}.
\]

The central moments also give
`n12+n21=8−2n11−n22/2`. Therefore `n22≤4n11`.

If `p=c=3`, (3) and `n22≤4` force `n22=4` and
`n13+n31=n11+n33=0`, contradicting this new inequality.
If `n22=2`, (3) gives `p+c−(n13+n31)=7`;
`n11≥1` forces `p=c=4,n11=1,n33=0`. If `n22=0`,
the same equation forces `p=c=4` and all four corner counts zero,
giving four each of the types `12,21,23,32`.
These prove (1) and the additional restrictions stated above.

The surviving incidence possibilities still require further argument;
no impossibility of all of them is asserted here.
