# Exact top-fiber capacity in a central-column image

Research note, 19 September 2026. These are unconditional finite
E1485 inequalities, not Lean declarations. They refine the usual
central-block packing bound by retaining the actual top degree of
the output and the top populations of the other fibers.

Write `r=min d`, `T` for the maximum-degree class, and fix a top
vertex `u` and a central vertex `z`. Put

\[
S=u*\operatorname{Col}(z),\qquad k=|C_u|,
\qquad q_e=|T\cap L_u^{-1}(e)|\quad(e\in S).
\]

There are `r` distinct members of `S`; exactly `k` are central.
Their `r` disjoint translation fibers, each of size `r`, partition
the fixed-parameter set `F_{z*u}(u)`. For a central member `e`,
its fiber is `Row(e)` and consists of `r` tops. Every other
member has `q_e≥1`, because it has an input in `Col(z)`.

For any `b∈S`, write `θ_b=|Row(b)∩T|`. The fixed-parameter
set contains `Row(b)`. Its `d(b)−θ_b` non-top members are
disjoint from all the top points counted in the fibers. Therefore

\[
\boxed{
d(b)-\theta_b+kr+
  \sum_{e\in S\setminus Z}q_e\le r^2.}                 \tag{1}
\]

In particular,

\[
\boxed{d(b)\le r^2-r-(r-1)|C_u|+\theta_b.}             \tag{2}
\]

The dual statements retain the actual top predecessor count of
the output and the central predecessor count of the right input.
If `b=u*v` is top, take a central successor `z` of `v`; then
`b∈S` and `d(b)=max d`. This gives the corresponding
pointwise restriction on every top-valued top product, without
replacing `θ_b` by a global upper bound.

When a noncentral member `a∈S` has no non-top successors except
its `σ_a` sharp successors, its fiber has exactly

\[
q_a=r-\sigma_a.                                      \tag{3}
\]

Indeed every sharp successor belongs to that fiber, and every
fiber input is an ordinary successor of `a`; these account for
all its non-top inputs. Thus (1) can retain exact contributions
from such low-degree outputs, instead of the generic bound one.

At order 48, minimum degree four, central count five, this gives
the sharper rowwise restrictions recorded in
[the five-central note](1485_order_forty_eight_five_central.md#3-finer-rowwise-capacities).
