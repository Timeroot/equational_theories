# When central parameters give the same auxiliary relation

Research note, 18 September 2026. This is a conditional pen-and-paper
criterion for full core, not a proof that the criterion always holds.

Let `M` be a finite E1485 magma with minimum translation degree `r`,
central set `Z`, and top set `T`. For central `h`, recall the
[two-sided auxiliary relation](1485_unrestricted_central_incidence.md)

\[
B_h(a)=a*Col(h),\qquad B_h^-(b)=Row(h)*b.
\]

It has exactly `r` predecessors and successors at every vertex.

**Criterion.** If `|T|=r²` and all relations `B_h`, `h∈Z`,
coincide, then the central core is full: `|Z|=r²`.

Indeed every top vertex has a central sharp successor, so
`T=⋃_{h∈Z}Col(h)`. For any top vertex `t`, independence of the
parameter gives

\[
t*T=\bigcup_{h\in Z}B_h(t)=B(t),\qquad |B(t)|=r.
\]

Every nonempty fiber of `L_t` has size `r`. The `r²` top inputs
therefore occupy all `r` fibers completely, with `r` top inputs
in each. A noncentral output `a=t*v` would have a non-top sharp
successor `f`; the good path `t→a⇒f` gives `t*f=a`, an
additional input in an already full fiber. This is impossible.
All products of top vertices are consequently central, which is
[equivalent to full core](1485_full_core_equivalences.md).

## A sufficient connectivity condition

Put an undirected graph on the central vertices: join `h,h'` if
their ordinary rows are equal or their ordinary columns are equal.
If the columns are equal, the successor formula above gives
`B_h=B_h'`. If the rows are equal, the predecessor formula gives
the same conclusion. Thus `B_h` is constant on every connected
component of this graph.

In particular, when `|T|=r²`, connectedness of this graph proves
full core by the criterion. Any non-full model with `r²` top
vertices must have at least two components. This does not assert
that the graph is connected in general, or that disconnectedness
alone implies a non-full core.
