# Equality in the top-product degree bound forces a matching

Research note, 18 September 2026. This is an unconditional finite
pen-and-paper theorem, not a Lean declaration. It does not assume
full core or any fixed number of translation degrees.

Let `n=rs` be the order of a finite E1485 magma, where `r` and `s`
are the minimum and maximum translation degrees. Write `T` for the
top-degree vertices and `Z` for the central, minimum-degree vertices.
Every product of two top vertices has degree at most `r²`.

**Theorem.** If `d(a)=r²`, the ordered pairs

\[
\{(u,v)\in T^2:u*v=a\}
\]

form a partial matching: no two distinct pairs have the same first
coordinate or the same second coordinate. Consequently their number
is at most

\[
\min\bigl(|\operatorname{TopPred}(a)|,
          |\operatorname{TopSucc}(a)|\bigr).
\]

In particular this bound is `r` whenever all vertices have exactly
`r` top neighbors in both directions.

## Proof

For an ordinary successor `a` of `u`, put

\[
F_u(a)=\{y:u*(a*y)=a\}.
\]

The [fixed-parameter identity](1485_image_research.md) gives

\[
|F_u(a)|=\frac{n^2}{d(u)d(a)}.
\]

The absorption identity `u*((u*v)*(v*y))=u*v` shows that
`Row(v)⊆F_u(a)` whenever `u*v=a`. If `u,v` are top and
`d(a)=r²`, then

\[
|F_u(a)|=\frac{r^2s^2}{sr^2}=s=|\operatorname{Row}(v)|.
\]

Finiteness therefore upgrades the inclusion to equality.
If `u*v=u*w=a` with `v,w` top, it follows that

\[
\operatorname{Row}(v)=F_u(a)=\operatorname{Row}(w).
\]

Every top vertex has a central sharp successor. Choose such a
successor `z` of `v`; the row equality makes it a successor of
`w` as well. Both paths `a→v→z` and `a→w→z` have central
endpoint and are consequently good. Uniqueness of the good middle
gives `v=a*z=w`.

The dual argument, using column sets and a central predecessor,
proves uniqueness in the other coordinate. This proves the theorem.

## Consequences at minimum degree three

The [three-central analysis](1485_three_central_minimum_top_output.md)
and the [five-central binary patterns](1485_five_central_binary_blocks.md)
both isolate a least-degree noncentral top product with at least four
good ordered top endpoint pairs. In their degree-six branch, a
separate top-fiber slot bound forces its degree to be nine. The
theorem above allows at most three pairs, a contradiction.

Thus the three-central case must have least noncentral degree four.
The five-central analysis now also proves its binary matrix structure
directly, using singleton-label counts. It therefore excludes **every**
five-central model at minimum degree three without an incidence-scan
premise.
