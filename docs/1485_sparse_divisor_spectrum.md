# Spectrum exclusions from sparse divisor intervals

Research note, 19 September 2026. These are new arithmetic consequences
of the finite structural results, not Lean declarations or a proof of
the complete spectrum conjecture.

**Conclusions.**

- For a prime `p` and `0≤e≤7`, order `p^e` belongs to the spectrum
  exactly when `p=2` or `e` is even. In particular every odd-prime
  fifth and seventh power is excluded.
- If `p<q` are primes with `q>p²`, order `p²q` is excluded. Order
  `pq²` is excluded unless `p=2`, when it is a known twice-square
  order.
- If `p,q` are primes with `q>p³`, order `p³q` is excluded.
  In particular, **`8q` is excluded for every prime `q≥11`**.
- For every prime `p`, order `3p²` is excluded. Among orders `9p`
  only `p=2` survives; among orders `6p` only `p=3` survives. Both
  surviving cases are order eighteen.

The prime-power and separated-prime conclusions have wholly analytic
proofs. The families involving a factor of three use
minimum-degree-three full-core results, now available
[without a degree-count restriction](1485_min_three_full_core.md),
with explicitly identified finite incidence checks. That dependency
must not be confused with a completely hand-classified proof.

## 1. The divisor-gap criterion

Let `r` be the minimum translation degree of a finite E1485 magma of
order `n`. Degree divisibility and reciprocity give

\[
r\mid n,\qquad r\le\sqrt n,\qquad
\{d(x):x\in M\}\subseteq\{d\mid n:r\le d\le n/r\}.
\]

The [first-top-output fiber theorem](1485_first_top_output_fibers.md)
says that a non-full central core supplies an occurring degree strictly
above `r` and at most `r²−2r+2`. Consequently, if no divisor of `n`
lies in that interval, the core is full. The
[full-core quotient theorem](1485_full_core_quotient.md) then gives

\[
\boxed{
\{d\mid n:r<d\le r^2-2r+2\}=\varnothing
\quad\Longrightarrow\quad n=r^2 2^j
\text{ for some }j\ge0.
}                                                   \tag{1}
\]

One can weaken the hypothesis by considering only divisors at most
`n/r`, since no larger degree occurs. For odd `n`, conclusion (1)
reduces to `n=r²`, so a nonsquare odd order cannot have such a
minimum degree.

In particular, at prime-power order `p^e`, minimum degree `r=p`
always gives full core: the first larger divisor is the excluded
endpoint `p²`, not a point of the open interval.

## 2. Odd-prime fifth and seventh powers

Let `p` be odd and suppose the order is `p^5`. The possible minimum
degrees are `1,p,p²`.

- At minimum one, the constant-row theorem would make the order a
  power of two.
- At minimum `p`, (1) would give `p^5=p²2^j`, impossible for odd `p`.
- At minimum `p²`, the only available degrees are `p²,p³`. Both
  occur, since they are the extreme degrees. The
  [two-degree cardinality theorem](1485_two_degree_lower_bound.md)
  would require `p³=2p²`, or `p=2`.

All cases are impossible.

For completeness, an odd prime order has only minimum one, and order
`p³` has minimum one or `p`; the same constant-row and two-degree
arguments exclude these. Even exponents up to four are squares and
have known constructions. Every power of two is a square or twice a
square, also with known constructions. This proves the stated
classification through exponent five. The new
[square-root divisor gap](1485_first_top_output_divisor_gap.md)
also excludes every odd prime seventh power: a non-full core of
prime-power order has minimum degree at least `p³`, while minimum
`p³` at order `p⁷` leaves only the two degrees `p³,p⁴`, which
have forbidden ratio `p`. Together with the square construction
at exponent six this gives the classification through exponent seven.

There is a useful description of the next possible frontier. If an
odd-prime nonsquare order `p^(2k+1)` has a model, its minimum degree
must be `p^i` with

\[
3\le i\le k-1.
\]

The cases `i=0,1,2` are now excluded by the gap; `i=k` leaves only the two
degrees `p^k,p^(k+1)`, again with forbidden ratio `p`. In particular,
the first prime-power exponent not excluded by this reasoning is
nine. At order `p^9`, any hypothetical model would have exactly

\[
p^3,\quad p^4,\quad p^5,\quad p^6
\]

as its degree values: minimum `p³` is forced, and omission of the
middle complementary pair would again leave only two degrees. This
is a remaining case, not an existence assertion.

## 3. Two widely separated prime factors

Let `p<q` be primes and suppose `q>p²`.

For `n=p²q`, the divisors at most `√n` are `1,p,p²`. Minimum
one is impossible because the order has an odd prime factor. Minimum
`p` has an empty open divisor interval `(p,p²)`, so (1) would make
`q` a power of two; this is impossible. At minimum `p²`, the only
degrees in `[p²,q]` are its endpoints. The two-degree theorem would
require `q=2p²`, contrary to primality. Thus `p²q` is excluded.

For `n=pq²`, the possible minima are `1,p,q`. Minimum one is again
impossible. At minimum `p`, the open divisor interval is empty, so
(1) would require `p²|n`, contrary to the exponent of `p` in `n`.
At minimum `q`, the only available degrees are `q,pq`; the two-degree
theorem forces `p=2`. Conversely `2q²` is a known twice-square
order. This proves both separated-prime claims.

The condition `q>p²` matters. This argument does not exclude all
orders involving two primes with one squared: closely spaced primes
can leave four available degree values at a larger minimum.

## 4. Three families reduced to minimum degree three

We use the established theorem that a minimum-degree-three model with
at most four distinct translation degrees has full core. Such a model
has order `9·2^j`. This invocation includes that theorem's finite
incidence dependencies.

First consider `n=3p²` with `p≥5`. The possible minima are
`1,3,p`. At minimum `p`, the only degrees are `p,3p`, which have
ratio three, contradicting the two-degree theorem. At minimum three,
there are at most the four degrees `3,p,3p,p²`, so full core would
give `3p²=9·2^j`, impossible. Minimum one is impossible too.
The remaining primes give orders twelve and twenty-seven, already
excluded by minimum-degree-two/full-core and odd-prime-cube arguments.
Thus no order `3p²` occurs.

Next let `n=9p` with `p≥5`. Besides minima one and three, the only
possible minimum is `min(9,p)`. Its degree interval contains just
`9,p`, so the two-degree theorem would require one to be twice the
other, impossible for the odd prime `p`. At minimum three the only
available degrees are `3,9,p,3p`, so full core forces `p=2^j`,
also impossible. The primes two and three give respectively the known
order eighteen and the excluded order twenty-seven.

Finally let `n=6p` with `p≥5`. Its possible minima are
`1,2,3,min(6,p)`. Minimum one is impossible; minimum two has full
core and would force `6p=4·2^j`. The last minimum leaves only the
degrees `6,p`, whose ratio cannot be two. At minimum three there
are at most four degrees, namely `3,6,p,2p`, and full core would
force `6p=9·2^j`, impossible. The primes two and three give the
excluded order twelve and the known order eighteen, respectively.

None of these arguments asserts that the union of selected degree
classes is a submagma. They only enumerate possible degrees of the
entire hypothetical model.

## 5. Odd order at minimum degree three

There is also an order-independent restriction:

\[
\boxed{r=3,\ n\text{ odd}\quad\Longrightarrow\quad n=9.}
\]

The [minimum-degree-three theorem](1485_min_three_full_core.md)
now gives full core at every order, with its explicitly listed finite
profile dependencies. Thus `n=9·2^j`, and oddness forces `j=0`.

This is a restriction on the minimum degree, not an exclusion of
other minima at the same order.

## 6. A cubed prime times a sufficiently large prime

Let `p,q` be primes with `q>p³`, and suppose `n=p³q` has a
finite model. The only divisors of `n` at most its square root
are `1,p,p²,p³`: any divisor involving `q` is larger than the
square root, while `p³` is smaller because `q>p³`.

Minimum one would make `n` a power of two, impossible. At minimum
`r=p` or `r=p²`, the next possible larger degree is at least
`pr`: all divisors below `q` are powers of `p`. The
[multiplicative divisor-gap theorem](1485_first_top_output_divisor_gap.md#4-multiplicative-gaps-between-occurring-degrees)
says that a non-full core with this gap requires `r>p²`.
Thus the core is full in both cases.

At `r=p`, full core would give `p³q=p²2^j`, so `pq` would
be a power of two, impossible for the distinct primes. At `r=p²`,
it would require `p⁴|p³q`, also impossible.

Finally, at `r=p³`, all degrees lie between `p³` and `q`,
and those endpoints are the only available divisors. The two-degree
theorem would give `q=2p³`, contrary to primality. All minima
have been excluded, proving

\[
\boxed{p,q\text{ prime},\ q>p^3
\quad\Longrightarrow\quad p^3q\notin\operatorname{Spec}(E1485).}
\]

For `p=2`, this gives all orders `8q` with prime `q≥11`.
It does not settle orders forty and fifty-six, where the separation
condition fails. No minimum-degree-three finite check is needed for
this family.
