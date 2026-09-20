# Good auxiliary paths force a block decomposition at the first top output

Conditional research theorem, 20 September 2026. This is a finite
pen-and-paper reduction, not a proof of full core. It isolates what the
[paired-top mixed-retraction target](1485_central_parameter_components.md#auxiliary-edge-transport-and-a-paired-top-target)
would imply at a first noncentral product of tops. No solver result is
used in the proof.

Let `n=rs`, with minimum translation degree `r`, central set `Z`, and
top set `T`. Suppose `x` has the least degree `p>r` of any noncentral
product of two tops. Write

\[
 U=TopPred(x),\quad V=TopSucc(x),\quad |U|=|V|=t,
 \qquad q=p-t,\quad k=r-q=r+t-p.
\]

The [first-output fiber theorem](1485_first_top_output_fibers.md) gives
`1≤q≤r−1`, so `1≤k≤r−1`. Each top left fiber at `x` consists of
all `q` non-top successors and exactly `k` tops. The dual statement
holds for the right fibers. The graph on `U×V` defined by `u*v=x`
is consequently `k`-regular in both directions.

**Additional hypothesis at this one vertex:** for every central `h`,
every path `a B_h x B_h b` is good. No goodness assumption at any
other middle vertex is needed below. This additional hypothesis is
not currently proved in general.

## 1. Every component of the good top-pair graph is complete bipartite

Choose a good top pair `a*d=x`, and a central `h` with `d∈Col(h)`.
Then `a B_h x`. By the additional hypothesis,

\[
 B_h(x)\subseteq L_a^{-1}(x).
\]

Both sets have size `r`, because `a` is top. Hence they are equal;
denote the common set by `J`. In particular `d∈B_h(x)`. Applying
the same argument to the predecessor direction gives

\[
 I:=B_h^-(x)=R_d^{-1}(x),\qquad |I|=|J|=r.
\]

Every pair in `I×J` is a marked path through `x`, so its product is
`x`. For any top `u∈I`, the `r`-point fiber `L_u^{-1}(x)` therefore
equals `J`; dually the right fiber at any top `v∈J` equals `I`.
Thus `I∩T` and `J∩T`, each of size `k`, form an entire connected
component `K_{k,k}` of the good top-pair graph.

Doing this for every component gives partitions

\[
 U=\bigsqcup_{i=1}^{\ell}U_i,\qquad
 V=\bigsqcup_{i=1}^{\ell}V_i,\qquad |U_i|=|V_i|=k,
\]

such that `u*v=x` exactly on the rectangles `U_i×V_i`. Therefore

\[
 \boxed{t=\ell k,\qquad p=r+(\ell-1)k,\qquad \ell\ge2.} \tag{1}
\]

The last inequality follows from `p>r`.

## 2. The central parameters split into matching classes

For `a∈U_i,d∈V_i`, define

\[
 S_i=\{h\in Z:a B_h x\}.
\]

Membership is equivalent to `x B_h d`: either marking, followed by
the `r`-point fiber argument above, supplies the other. That argument
also shows that `B_h^-(x)=I` and `B_h(x)=J` whenever `h∈S_i`.
Consequently the definition is independent of the choices `a,d` in
the component.

Writing `P_u=Col(u)∩Z`, `C_v=Row(v)∩Z`, the two auxiliary
descriptions give

\[
 \boxed{S_i=\bigsqcup_{u\in U_i}P_u
             =\bigsqcup_{v\in V_i}C_v.}                  \tag{2}
\]

For example, `a B_h x` means that a top input in `Col(h)` lies
in `L_a^{-1}(x)`, whose top portion is exactly `V_i`. The dual
description gives the first union. The `P`-blocks of all of `U`
partition `Z`, as do the `C`-blocks of all of `V`, by uniqueness
of paths with a central endpoint. Thus the `S_i` are nonempty and
partition `Z`.

Every `P_u∩C_v` has size at most one. The two partitions of `S_i`
in (2), each with `k` nonempty blocks, therefore give

\[
 \boxed{k\le |S_i|\le k^2,\qquad
 t\le |Z|\le \ell k^2=kt=k(p-r+k).}                    \tag{3}
\]

## 3. Exact central mixed-retraction behavior at `x`

If `h∈S_i`, the central path `h→h*x→x` puts `h*x` in `U_i`;
dually `x*h∈V_i`. It follows that

\[
 \boxed{\lambda_{h,j}(x)=x
 \quad\Longleftrightarrow\quad h,j\text{ belong to the same }S_i.}
                                                               \tag{4}
\]

For parameters in different classes, the two top endpoints
`h*x∈U_i`, `x*j∈V_l` have a bad path through `x`. Their product
has degree below `p`, and so is central by minimality of `p`.
In particular `λ_{h,h}(x)=x` for every central `h`, even though
the off-diagonal central mixed retractions can move `x` to `Z`.
The separate one-parameter band identities do not by themselves
contradict such an equivalence-relation pattern.

There is also a constraint on overlaps between different classes. If
`h∈S_i`, `j∈S_l`, and `i≠l`, then

\[
 |Row(h)\cap Row(j)|\le q,\qquad
 |Col(h)\cap Col(j)|\le q.                              \tag{4a}
\]

Indeed `B_h^-(x)` and `B_j^-(x)` intersect exactly in the common
`q` non-top predecessors of `x`. The map `t↦t*x`, injective on
`Row(h)`, sends `Row(h)∩Row(j)` into that intersection. The
column statement is dual. Thus overlap in more than `q` neighbors
forces two central parameters into the same class; no general packing
contradiction from this condition is asserted.

## 4. The adjacent-degree consequence and the remaining premise

If `p=r+1`, equation (1) forces `k=1` and `ℓ=2`; then (3) gives
`|Z|≤2`. Since the general central-count bound is `|Z|≥r`,

\[
 \boxed{r\ge3,\ p=r+1\quad\Longrightarrow\quad
 \text{some }a B_h x B_h b\text{ is bad}.}                \tag{5}
\]

Thus proving the additional local-goodness hypothesis at every first
top output would exclude all adjacent-degree first-output branches.
Equation (5) is not itself such an exclusion: the local hypothesis
remains unproved. For general `p`, the decomposition above also does
not rule out `\ell≥2` or establish full core.
