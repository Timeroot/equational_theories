# E1483: permutation constructions and geometric obstructions

26 September 2026. This pass gives general constructions, rather than new
individual orders. **It does not enlarge the currently proved spectrum beyond
squares and twice squares.** The permutation constructions and the implication
from group-affine E1483 to E168 are proved in Lean. The projective-plane
obstruction below has a complete mathematical proof, but no Lean formalization.
The additional finite searches are explicitly separate from these theorems.

Write E1483 as

\[
                 (y*x)*(x*(y*z))=x.
\]

## 1. Arbitrary permutations on triangles

Choose an index set I, sets S_i, and, independently for every triple i,j,k,
a permutation p_ijk of S_j. An element is an ordered pair
`((i,a),(j,b))`, with a in S_i and b in S_j. Define

\[
 ((i,a),(j,b))*((k,c),(l,d))
   =\bigl((j,p_{ijk}^{-1}(b)),(k,p_{jkl}(c))\bigr).
\]

This satisfies **E168**, and hence E1483. Indeed, writing x,y,z with index
pairs (i,j),(k,l),(m,n), respectively, the two fiber coordinates in
`(y*x)*(x*z)` are

\[
 p_{lij}^{-1}(p_{lij}(a))=a,
 \qquad p_{ijm}(p_{ijm}^{-1}(b))=b.
\]

There are no compatibility conditions on the permutations. In particular,
they need not be linear, commute, or come from a common group action. The
sets S_i can have different sizes. The finite order is

\[
                         \left(\sum_i |S_i|\right)^2.
\]

This includes graphs different from the natural central groupoid, not just
different labels on that example. Take I={0,1}, S_0=S_1={0,1}, let p_000
interchange the two elements, and let all other permutations be identities.
This gives a 16-element central groupoid with **six distinct row images**.
The natural central groupoid of order 16 has four, so they are not isomorphic.
For j=1 the row image depends on b alone, giving two images. For j=0 its
two first-fiber entries, indexed by k, are `(1-b,b)` if i=0 and `(b,b)` if
i=1, giving four more images.

In graph language these are directed graphs with a unique two-step path
between every ordered pair. The permutations change how the intermediate
vertices are assigned while retaining that property. Multiplying these
models by a Boolean NAND cube, and using the already proved cubic twists,
gives further E1483 models at square and twice-square orders.

Lean: `Spectrum.E1483.PermutationCover.triangle_central`, `triangle_lawful`,
and `triangle_card` in
[PermutationCover.lean](../equational_theories/Spectrum/Equation1483/PermutationCover.lean).

## 2. Permutation extensions of any E1483 model

Let f be any E1483 operation on G. Make a finite graph of coefficient
positions `A(x,y)` and `B(x,y)` by adding the edges

\[
\begin{aligned}
 B(f(y,x),f(x,f(y,z)))&\sim A(y,x),\\
 A(f(y,x),f(x,f(y,z)))&\sim B(x,f(y,z)).
\end{aligned}
\]

Assign an arbitrary permutation p_C of a set S to each connected component
C. Denote the permutations at A(x,y), B(x,y) by a_xy, b_xy. Then

\[
 (x,u,v)*(y,w,t)
       =\bigl(f(x,y),b_{xy}^{-1}(v),a_{xy}(w)\bigr)
\]

is an E1483 operation on `G × S × S`. In the E1483 word, the first coordinate
reduces by the original law, and the other two coordinates reduce by the
two inverse-permutation cancellations encoded by the displayed edges.
Thus every component supplies an independent permutation parameter. The
finite order is `|G| |S|²`.

This is a construction from a graph computed from the base multiplication
table; it requires no model search. The cubic Boolean example

\[
 f(x,y)=\neg(\rho(x)\mathbin{\&}\rho^2(y)),
 \qquad x,y\in\{0,1\}^3,
\]

where rho cyclically permutes the three coordinates, gives **27 components**.
We generated 100 deterministic random choices of binary permutations, giving
100 presentations of order 32, and verified E1483 directly in each one.
These are not claimed to be 100 isomorphism classes. Their common row-rank
profile is `2:4, 4:12, 8:12, 16:4`. Three full tables and their parameters
are saved in the research record.

The open projector identities and the two rank-descent candidates from the
[previous pass](1483_rank_descent_followup.md) survived these 100 examples.
This is finite evidence, not a proof. The [28 September follow-up](1483_fo_untwist_research.md)
proves in Lean that the first saved example cannot untwist to E1485 by any
cubic automorphism. It nevertheless admits a different FO-definable E1485
operation, also proved in Lean.

Lean: `Spectrum.E1483.PermutationCover.extension_lawful` and `extension_card`.

## 3. Weighted covers: a way to vary cardinalities

Suppose an E1483 magma G maps homomorphically to the natural central
groupoid `I × I`. Write its two coordinate maps as l,r, so that

\[
 l(x*y)=r(x),\qquad r(x*y)=l(y).
\]

Choose sets S_i of arbitrary sizes w_i. Replace x by the elements
`(x,a,b)` with a in S_l(x) and b in S_r(x), and define

\[
                  (x,a,b)*(y,c,d)=(x*y,b,c).
\]

This is well-defined and satisfies E1483 by direct substitution. If m_ij
is the number of elements of G mapping to (i,j), its order is

\[
                         \sum_{i,j}m_{ij}w_iw_j.
\]

Unlike a uniform direct product, this gives a quadratic family of orders
from one base model. It is also a fiber product with a natural central
groupoid. For the familiar `NAND × central(I)` model, m_ij=2, so this still
gives only `2(Σw_i)²`. A base with a different fiber matrix could make this
construction useful for the open spectrum; **no such useful base was found
in this pass**.

Lean: `Spectrum.E1483.PermutationCover.weighted_lawful` proves preservation
of E1483. The displayed finite counting formula is elementary counting of
the fibers; it is not separately formalized in that file.

## 4. All group-affine attempts collapse to E168

**Theorem.** Let H be any group, A,B endomorphisms, and c in H. If

\[
                            x*y=A(x)B(y)c
\]

satisfies E1483, it satisfies E168. No finiteness, commutativity of H, or
commutation of A and B is assumed.

Here is a proof. Products of endomorphisms below mean composition. Expanding
E1483 gives

\[
 A^2(y)AB(x)A(c)BA(x)B^2A(y)B^3(z)B^2(c)B(c)c=x.
\]

Set all variables to 1, then vary z, to obtain

\[
 A(c)B^2(c)B(c)c=1,\qquad B^3(z)=1.
\]

Put d=A(c) and cancel the constant suffix. The remaining equations are

\[
\begin{aligned}
 A^2(y)AB(x)dBA(x)B^2A(y)&=xd,\\
 AB(x)dBA(x)&=xd,                                      \tag{1}\\
 A^2(y)dB^2A(y)&=d.                                    \tag{2}
\end{aligned}
\]

The first equation and (1),(2) show that A²(y) commutes with every x.
Apply B to (2): BA² is trivial because B³ is trivial. Substituting A(x)
in (1) therefore gives ABA=A. Applying A to (1), and commuting the central
element A²(c) past A(x), now gives A²B=1. Substitute B(x) in (2) to get
B²AB=1. Finally, apply B² to (1): it gives B²=1. Equation (2) then gives
A²=1. Here `=1` means the trivial endomorphism.

With A² and B² trivial, the expansion of `(y*x)*(x*z)` reduces to the same
expression as (1), followed by `B(c)c=d⁻¹`. Its value is x, proving E168.

This proof is checked in Lean as
`Spectrum.E1483.GroupAffine.central` and `lawful_iff_central` in
[GroupAffine.lean](../equational_theories/Spectrum/Equation1483/GroupAffine.lean).
The main theorem uses only `propext`. Consequently a finite example in
this entire class has square order, by the existing E168 spectrum theorem.

For abelian groups this also identifies the coefficient algebra. Expanding
first gives

\[
 AB+BA=I,\quad A^2+B^2A=0,\quad B^3=0.
\]

These force A²=B²=0. The four endomorphisms AB,A,B,BA are matrix units for
the 2-by-2 matrix ring: the group decomposes into two isomorphic summands,
and the operation, after removing its constant offset, is the natural
central operation `(u,v)*(s,t)=(v,s)`. This explains why using larger
matrices or noncommuting ring coefficients does not escape square orders.

## 5. Projective planes: a general obstruction

The vector cross-product identity suggests projectivizing
`(y × x) × (x × (y × z))`: in the generic case the result is proportional
to x. The zero and degenerate cases cannot be repaired by the natural
projective-incidence completion, as follows.

Let P be a finite projective plane of order q≥2, with a correlation pi.
Put `u → v` when v lies on the line pi(u), and let h=pi² on points. Thus

\[
                   u\to v\quad\Longleftrightarrow\quad v\to h(u).
\]

Suppose a product f(u,v) always selects an intermediate point on a path
`u → f(u,v) → v`. We claim it cannot satisfy E1483.

Write R(u) for the successor line and C(v) for the predecessor line.
These lines coincide exactly when v=h(u); otherwise their intersection
is a single point, so the product is forced. Also **every** point of R(u)
occurs as a product f(u,z): if w is in R(u), choose z in R(w) other than
h(u), and the unique intermediate is w.

Fix a point a. For each x in R(a) other than possibly h⁻¹(a), the distinct
lines C(a) and R(x) have q points in their difference. Choose

\[
                y\in C(a)\setminus R(x),\qquad y\ne h^{-1}(x).
\]

This is possible because q≥2. Then `y → a → x` and x≠h(y), so f(y,x)=a.
We also have `x → h(a)`, hence h(a) is in R(x) and y≠h(a). Let b be the
intersection of the distinct lines R(y) and R(h(a)). Because
`y → h(x)` is equivalent to `x → y`, our choice of y ensures b≠h(x).
Thus the path `x → h(a) → b` has unique intermediate and f(x,b)=h(a).

Since b lies in R(y), choose z with f(y,z)=b. E1483 now forces

\[
                    f(a,h(a))
             =f(f(y,x),f(x,f(y,z)))=x.
\]

There are at least q≥2 choices of x, a contradiction. This proof applies
to non-Desarguesian planes as well, whenever the specified correlation
exists. It rules out this construction, **not every magma of order
q²+q+1**. Covers that replace a point by multiple elements are not covered
by this proof.

Before finding the argument, direct propagation refuted all 168 bilinear
correlations over F₂ and all 5,616 over F₃, modulo nonzero scalar. Those
computations are consistent with, but not needed for, the proof.

## 6. Other construction searches and their limits

The archived searches also tried:

* Every subalgebra of the cubic Boolean model at order 8, its square at
  order 64, and its products with natural central models at orders 32 and
  72. There were respectively 5,29,15,35 nonempty subalgebras. None had a
  new spectrum value.
* Extensions over the four-point natural central quotient with unequal
  fiber sizes, at total orders 12 and 13. All 13 tested fiber patterns
  were refuted. These patterns satisfy the necessary inequalities
  `m_ij ≤ m_ki m_jk`; the two-element diagonal fibers were normalized
  using the exhaustive two-element classification. No claim that these
  quotient searches cover arbitrary models of orders 12 or 13 is made.
* Two-element covers of two Fano correlation graphs (order 14), a
  two-element cover of the standard F₃ polarity graph (order 26), and
  a three-element cover of the standard Fano polarity graph (order 21).
  All were refuted within their 90-second budgets.
* The Kneser graph KG(6,2), with its 15 two-element subsets and disjointness
  edges, selecting products among common neighbors. This was also refuted.

These last three items are external SAT results without Lean certificates.
They impose additional construction assumptions and **do not exclude the
corresponding orders from the E1483 spectrum**. None of the new research
data changes the spectrum catalogue or website proof status.

The exact source scripts, tables, search records, and logs are in
[the research archive](../data/spectrum/1483_construction_sources.tar.gz).
The [record](../data/spectrum/1483_general_constructions.json) includes
checksums and full positive examples. Reproduce the positive constructions
and validate the saved record with:

```sh
python3 scripts/spectrum_1483_constructions.py
lake build equational_theories.Spectrum.Equation1483.GroupAffine \
  equational_theories.Spectrum.Equation1483.PermutationCover
```

The checker verifies the actual multiplication tables and coefficient
relations, not merely their recorded solver status. To rerun the exploratory
searches, unpack the archive in a fresh directory and run its Python scripts;
the SAT scripts require `python-sat`, and the candidate-identity scan requires
NumPy. Their UNSAT reports still are not Lean proofs.
