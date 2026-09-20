# Computational lead: two complete degree-four profile rows

Research log, 18 September 2026. **This is not a new theorem.**
The solver outcomes below have neither a checked refutation certificate
nor a pen-and-paper replacement. The proved degree-four class bound
remains [eight](1485_three_central_saturated_four.md).

The executable [profile filter](../scripts/1485_three_central_profile_scan.py)
preserves an independently inspected necessary-constraint encoding.
It requires the `z3-solver` Python package. It is a partial-incidence
search, not a search through complete magma tables; SAT survivors
must not be called E1485 models.

## The question and observed outcomes

In a hypothetical finite minimum-degree-three magma with three central
vertices, degree-four vertices have permutation-transversal top profiles.
When their reciprocal class has at least three vertices, all predecessor
profiles have one parity and all successor profiles the opposite parity.
Write these profiles as `P_p,Q_q`, and `t_pq=P_p∩Q_q`.

The main lead asks whether six selected degree-four vertices can fill
two complete rows of the `3×3` profile grid. The selected vertices
need not exhaust the degree-four class. Twelve reciprocal-class labels
suffice for the union of their sharp predecessor and successor images.

Observed outcomes in this research session:

- Six selected vertices in two full rows, without surjectivity onto the
  reciprocal labels: UNSAT for all six affine coordinate normalizations.
- Eight vertices exhausting the degree-four class, reciprocal class
  sizes three through six: UNSAT in all 24 combinations with those
  coordinate normalizations.
- The six-vertex test still gives UNSAT without the optional unique-top-
  middle constraints at normalization `(epsilon,delta)=(1,0)`.
- Removing the dual-law constraints gives SAT at that normalization.

These are computational observations. In particular, **the two-full-row
obstruction has not been promoted to an analytic or Lean theorem**.

## Encoding audit

Normalize the central successor and predecessor labels to

\[
C(t_{pq})=p+q,\qquad H(t_{pq})=\epsilon(p-q)+\delta
\quad\text{over }\mathbb F_3,
\]

where `epsilon=±1` and `delta=0,1,2`. Rescaling and translating
profile indices gives these six relative normalizations. The two-full-
row shape is unchanged up to profile row/column relabeling.

For each selected vertex `a`, `F(a),G(a)` name its unique sharp
successor and predecessor. An `F` fiber has distinct predecessor-profile
indices, a `G` fiber has distinct successor-profile indices, and the
pair `(G(a),F(a))` determines `a`. These constraints follow from
uniqueness of good paths containing a sharp edge. Restricted-growth
labels for `F` only remove reciprocal-label permutations.

For every reciprocal label `b`, `out[b]` and `in[b]` describe its
three ordinary top successors and predecessors. They meet each central
successor-label class and predecessor-label class, respectively, once.

For a top input `t`, `left[a,t]=-1` means `a*t=F(a)`, equivalently
`t∈out[F(a)]`; `right[a,t]=-1` means `t*a=G(a)`, equivalently
`t∈in[G(a)]`. A nonnegative value indexes a top output by the
central equality which would be forbidden in the corresponding law:

\[
\begin{aligned}
left[a_{pq},t]=j&\quad\Rightarrow\quad
a_{pq}*t=t_{\epsilon(p+j-\delta)+q,\ q},\\
right[a_{pq},t]=i&\quad\Rightarrow\quad
t*a_{pq}=t_{p,\ \epsilon(i-q)+\delta-p}.
\end{aligned}
\]

If `F(c)≠G(a)` and `F(d)≠G(c)`, the products `c*a` and
`d*c` have their unique ordinary top middles. Substitution into
E1485 forbids `left[a,t_(P(c),Q(d))]=Q(c)`. The reversed pair
of inequalities in the script similarly imposes the dual law's
forbidden right output.

The shared ordinary top-adjacency matrix `D` has exactly one successor
in every central successor-label class and one predecessor in every
central predecessor-label class. Each asserted top-valued mixed product
must give its actual ordinary edge in `D`. Optional constraints also
require its ordinary top middle to be unique when the sharp middle
is absent. No symmetry assumption on `D` or on squaring is imposed.

## Reproduction and next step

For the six-vertex local test, run each `epsilon=1,-1` and
`delta=0,1,2` in:

```sh
python3 scripts/1485_three_central_profile_scan.py --size 6 --reciprocal 12 --ordinary --partial --epsilon 1 --delta 0 --timeout 10
```

For the eight-vertex test, use `--size 8`, omit `--partial`, and
run reciprocal sizes `3,4,5,6` with the same six normalizations.
The timeout is a solver limit, not a guaranteed total runtime;
`unknown` must not be counted as UNSAT.

The next mathematical task is to derive a contradiction from the
two full profile rows using E1485, its dual, and the shared ordinary
top adjacency. A checked finite proof of the encoding's infeasibility
would be an alternative, but none has been supplied here.
