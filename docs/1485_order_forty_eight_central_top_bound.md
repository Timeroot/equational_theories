# Eight central elements allow only fifteen through nineteen tops

Research theorem, 20 September 2026. This is an independently audited
analytic restriction, not an exclusion of the whole eight-central case
or a Lean theorem. No enumeration or SAT result is used.

Assume order forty, minimum degree four, and eight central elements.
Write `Z,A,B,T` for the degree classes `4,5,8,10`, with respective
sizes `8,a,b,h`. Let `q` count members of `A` with three top
neighbors; the other `a−q` have four. Thus

\[
 a+b=32-h,\qquad0\le q\le a,\qquad b\le a+q.
\tag{1}
\]

The last inequality counts sharp neighbors: every `B` vertex has one,
while the `A` vertices contribute `a+q` incidences in each direction.

**Theorem.**

\[
                     15\le h\le19,\qquad
                     4a+q\le160-7h.
\tag{2}
\]

## 1. The weighted degree-five capacity

Every central block has size one, two, or three by the
[full-block exclusion](1485_order_forty_ten_central_full_blocks.md).
For a top, write `P,C` for its two block sizes and `α` for its
number of successors in `A`. The
[degree-five support bound](1485_order_forty_eight_central_high_five.md#1-central-parameter-capacity-excludes-twelve-degree-five-elements)
gives `α≤f(C)`, where `(f(1),f(2),f(3))=(4,3,1)`.

Let `t` count triple `C` blocks and put `X=Σ_(C=1)P`.
The central moments give

\[
 \sum1=h,\quad\sum P=\sum C=32,\quad\sum PC=64.
\]

Since `f(C)=7−2C−1_(C=1)`, and the singleton count is
`2h−32+t`,

\[
 \sum Pf(C)=96-X,\qquad \sum f(C)=5h-32-t.
\]

On the other hand `Σα=4a−q` and `ΣPα=8a`. Therefore

\[
 4a+q=\sum(P-1)\alpha
 \le128-5h+t-X\le160-7h,                                \tag{3}
\]

where the last inequality uses `X≥2h−32+t`. All terms discarded
here are nonnegative; this will matter at equality.

## 2. Twenty-one tops are impossible

For block sizes at most three, the two inequalities

\[
 0\le\sum(3-P)(3-C)=9h-128
 \le2\sum(3-P)=6h-64
\]

give `15≤h≤21`. At `h=21`, (3) gives `4a+q≤13`, whereas
(1) gives `2a+q≥11`. Subtraction forces `a≤1`, contrary to
`3a≥2a+q≥11`.

## 3. Equality at twenty tops forces impossible central rows

At `h=20`, the corresponding inequalities are

\[
                     4a+q\le20,\qquad2a+q\ge12.
\]

They force `a≤4`, while `q≤a` forces `a≥4`. Hence
`a=q=4`, `b=8`, and both inequalities are equalities.

Equality throughout (3) has two consequences:

- Every top with `C=1` has `P=1`. The dual statement gives the
  converse: singleton blocks are paired only with singleton blocks.
- Whenever `P>1`, its value is `α=f(C)`.

If a top has `C=2`, it consequently has `P>1` and `α=3`.
A central row containing it has one of the block patterns
`3311,3221,2222`; only the last two contain doubles, and each
contains at least two. Their `α` sum would be at least six,
contrary to its exact value `a=4`. Thus no double block occurs;
the dual argument excludes predecessor doubles as well.

Only block types `(1,1)` and `(3,3)` remain. With twenty tops,
the block-size sum thirty-two would force six of type `(3,3)`
and fourteen of type `(1,1)`. Their product moment is
`6·9+14=68`, not 64. This contradiction excludes `h=20`
and completes the proof.

At nineteen tops the remaining numerical cases in (1)–(3) are
`a=5,3≤q≤5` or `a=6,1≤q≤3`. The subsequent
[central-row deficit argument](1485_order_forty_eight_central_nineteen_tops.md)
excludes both, sharpening the top-count range to **`15≤h≤18`**.
