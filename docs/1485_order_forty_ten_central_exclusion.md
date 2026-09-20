# Order forty cannot have ten central elements

Research proof, 20 September 2026. This is an independently audited
analytic finite E1485 exclusion, not a Lean theorem. It uses no
enumeration or SAT premise.

**Theorem.** A finite E1485 magma of order forty and minimum degree
four cannot have ten central elements.

Suppose such a magma exists. Write `Z,T,A,B` for the degree classes
`4,10,5,8`, respectively, and put `h=|T|`, `a=|A|`, `b=|B|`.
The [ten-central reduction](1485_order_forty_ten_central_small_blocks.md)
gives `h∈{17,18}`. The
[full-block theorem](1485_order_forty_ten_central_full_blocks.md)
gives

\[
1\le |P_u|,|C_u|\le3\qquad(u\in T),
\]

where `P_u=Col(u)∩Z` and `C_u=Row(u)∩Z`. Each central row
and column contains four tops; their opposite central blocks
partition the ten central elements. Their block-size pattern is
therefore always `3331` or `3322`.

The [first-output reduction](1485_order_forty_four_central_exclusion.md#4-precisely-what-remains-at-order-forty)
gives four top neighbors and one sharp `B` neighbor in each direction
at every member of `A`. Since each member of `B` has a sharp `A`
neighbor, counting sharp edges gives `a≥b`. Thus

\[
a+b=30-h\in\{12,13\},\qquad a\ge6.
\tag{1}
\]

## 1. A top-to-degree-five edge uses at least seven central parameters

For a top `u`, let `α_u` count its ordinary successors in `A`.
Suppose `u→x`, with `x∈A`. Its top predecessor and successor
profiles have size four, and its good top-product matrix is the
complement of a permutation matrix. Consequently the four-element
fiber `L_u^{-1}(x)` contains its one sharp successor in `B` and
exactly three of its four top successors.

For a central parameter `z`, the auxiliary relation is
`B_z(u)=u*Col(z)`, and multiplication by `u` is injective on
`Col(z)`. Thus the set of parameters for which `u B_z x` is the
union of the `C` blocks of those three top inputs. All four `C`
blocks in `TopSucc(x)` partition `Z`; the omitted block has size
at most three. Therefore

\[
\#\{z\in Z:u\mathrel{B_z}x\}\ge7.
\tag{2}
\]

Each `B_z` is four-regular and contains every sharp edge. In
particular all `|C_u|` outgoing central edges at `u` belong to
every `B_z`. Summing the remaining outgoing capacity over the ten
parameters and using (2),

\[
7\alpha_u\le10(4-|C_u|).
\]

The resulting integer bounds are

| Size of `C_u` | 1 | 2 | 3 |
| ---: | ---: | ---: | ---: |
| Upper bound for `α_u` | 4 | 2 | 1 |

The dual bounds hold for the number of predecessors in `A`, using
`|P_u|` in place of `|C_u|`.

For each central `z`, the four tops in `Row(z)` satisfy

\[
\sum_{u\in Row(z)}\alpha_u=a.
\tag{3}
\]

Indeed every `x∈A` has exactly one top middle on a path from `z`
to `x`, and every path with a central endpoint is good. A central
row of type `3331` has capacity at most `1+1+1+4=7`; a row of
type `3322` has capacity at most `1+1+2+2=6`. Hence `a≤7`.
Together with (1),

\[
a\in\{6,7\}.
\tag{4}
\]

## 2. Seven degree-five elements give a parity contradiction

If `a=7`, every central row must have type `3331`; thus no top
has a size-two `C` block. The dual argument excludes size-two
`P` blocks. All central blocks have size one or three.

If `h=17`, the seventeen odd `C`-block sizes cannot sum to forty.
Thus `h=18`, in which case exactly seven `C` blocks have size one.
Every central row contains exactly one
such top, meaning that the `P` blocks at those seven tops partition
`Z`. Their sizes are all odd, so their sum is odd. It cannot equal
`|Z|=10`. This excludes `a=7`.

## 3. Six degree-five elements give two incompatible partitions

Suppose `a=6`. Then `a≥b` and `a+b∈{12,13}` force `b=6`
and `h=18`. In a central row of type `3322`, all four bounds
in §1 must be attained. Thus every size-two `C` block has `α=2`,
and any size-three `C` block appearing in such a row has `α=1`.

A top with a singleton `C` block lies in a row of type `3331`.
The other three tops have `α≤1`, so its own value is at least
three. It is therefore three or four. Tops with size-three `C`
blocks have `α=0` or `1`.

Define

\[
R=\{u\in T:|C_u|=3,\ \alpha_u=0\},\qquad
S=\{u\in T:|C_u|=1,\ \alpha_u=4\},
\]

and put `x=|R|`, `y=|S|`. Relative to the baseline value
`4−|C_u|`, precisely the tops in `R` decrease `α` by one and
the tops in `S` increase it by one. Every `A` vertex has four
top predecessors, so

\[
24=\sum_{u\in T}\alpha_u
=4|T|-\sum_{u\in T}|C_u|+y-x
=32+y-x.
\]

Hence

\[
x-y=8.
\tag{5}
\]

Now look at one central row. If it is `3322`, it contains no
member of `R` or `S`. If it is `3331`, its `α` values are
either `1,1,1,3` or `1,1,0,4`. In the first case it again
contains neither set; in the second it contains exactly one member
of each. It follows that

> The `P` blocks indexed by `R` and those indexed by `S` each
> partition the same subset of `Z`.

All these blocks are nonempty, and each has size at most three.
The first partition gives `x≤10`. Equality of the covered subsets
also gives

\[
x\le\sum_{u\in R}|P_u|
=\sum_{v\in S}|P_v|\le3y.
\]

But (5) and `x≤10` imply `y≤2`, hence `x≤6`, whereas (5)
requires `x≥8`. This contradiction excludes `a=6` and completes
the proof.

## Consequence

The proof excludes both seventeen and eighteen tops in one argument.
The earlier [seventeen-top proof](1485_order_forty_seventeen_tops.md)
is an independent longer exclusion, not a dependency here.

This does not exclude the other remaining central counts at order
forty, and it does not establish the full E1485 spectrum conjecture.
The earlier [eighteen-top reduction note](1485_order_forty_ten_central_eighteen_tops.md)
contains independent quantitative restrictions, but none of its
excess or internal-graph calculations is needed for this proof.
