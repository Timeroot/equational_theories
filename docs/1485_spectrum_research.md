# E1485: toward the square / twice-square spectrum

Research record, 17 September 2026. **The general converse remains open in
this work.** This note proves two restricted converse results and records the
obstacles to extending them. This is a mathematical development, not a new
Lean proof: no spectrum facts, pending axioms, or definability-board entries
are changed.

Write the weak central groupoid identity as

\[
  (y*x)*(x*(z*y))=x. \tag{W}
\]

The conjecture is that a nonempty finite model has order \(k^2\) or
\(2k^2\), for an integer \(k\geq1\). If empty carriers are allowed, order
zero is also present and is already a square.

## What is proved here

| Statement | Status and proof |
|---|---|
| Every square and twice-square order occurs | Known construction; recalled below; already in Lean |
| A finite model in the specified high/low graph family has order \(2k^2\) | Complete matrix argument below, finishing the counting route in the discussion |
| If \(0*x=x*0=1\), then \(T(x)=x*1\) satisfies \(T^{10}=\mathrm{id}\) | Complete short algebraic argument below; no finiteness needed |
| Every model with such a constant row and column is a Boolean NAND algebra twisted by an automorphism \(\sigma\) with \(\sigma^5=\mathrm{id}\) | Complete reduction below; two equational lemmas have explicit rewrite derivations in the appendix |
| Finite models with a constant row and column have exactly power-of-two orders | Consequence of the classification |
| Every finite E1485 model has square or twice-square order | **Not proved**; neither restricted hypothesis is established for arbitrary models |

“Complete” here means a supplied mathematical argument, including the
explicit equational derivations where indicated; it does **not** mean checked
in Lean. The standard Boolean-algebra single-axiom theorem used at the end is
already formalized in
[Sheffer.lean](../equational_theories/Sheffer.lean). No argument here uses the
reported order-11 or order-13 exclusions.

## 1. Existence and the graph formulation

On \(S\times S\), put

\[
 (a,b)*(c,d)=(b,c).
\]

This satisfies the stronger central groupoid law
\((y*x)*(x*z)=x\), hence (W), and gives every square order. The
two-element NAND algebra, \(u*v=1-uv\), satisfies (W). Its direct product
with the preceding model gives every twice-square order. The existing Lean
declarations are `Spectrum.square_1485` and `Spectrum.twice_square_1485`
in [Constructions.lean](../equational_theories/Spectrum/Constructions.lean).

We use the already-established dual identity

\[
 ((y*z)*x)*(x*y)=x. \tag{D}
\]

For completeness, write \(z=z_1*z_2\), where
\(z_1=z*z\) and \(z_2=z*(z*z)\), using (W). If \(w=y*z\),
another instance of (W) gives \(y=(z_2*y)*w\). Thus
\((w*x)*(x*y)=(w*x)*(x*((z_2*y)*w))=x\), proving (D).

The associated directed graph has \(a\to b\) iff \(b=a*z\) for
some \(z\), equivalently iff \(a=w*b\) for some \(w\). A two-edge
path is *good* when its middle vertex is the product of its endpoints.
There is exactly one good path between each ordered pair of vertices.
The five-cycle rule says that in
\(a\to b\to c\to d\to e\to a\), goodness of the first and third
two-edge paths implies goodness of \(b\to c\to d\). See the
[blueprint chapter](../blueprint/src/chapter/weak_central_groupoids.tex) and
[WeakCentralGroupoids.lean](../equational_theories/WeakCentralGroupoids.lean).

## 2. A complete converse for the high/low graph family

Assume a finite graph model has a partition into **nonempty** sets \(L,H\)
such that:

1. There are no \(H\to H\) edges.
2. A two-edge path is good exactly when it is not entirely in \(L\).

These are extra hypotheses. In particular, merely having a homomorphism to
the two-element magma does **not** assert the second condition.

Let \(|L|=k\), \(|H|=m\), and write the adjacency matrix as

\[
 M=\begin{pmatrix}A&B\\C&0\end{pmatrix}.
\]

Counting the unique good two-edge path between each pair gives

\[
 AB=J_{k,m},\quad CA=J_{m,k},\quad
 BC=J_{k,k},\quad CB=J_{m,m}, \tag{1}
\]

where \(J_{s,t}\) is the all-ones matrix. The rectangular trace identity
\(\operatorname{tr}(BC)=\operatorname{tr}(CB)\) gives \(k=m\).
All blocks are now square; write \(J=J_{k,k}\).

Since \(BC=CB=J\), associativity gives \(BJ=JB\) and \(CJ=JC\).
An integer matrix commuting with \(J\) has a common row and column sum:
indeed, \((BJ)_{ij}\) is row sum \(i\), and \((JB)_{ij}\) is
column sum \(j\). Call these common sums \(b\) and \(c\).
But

\[
 CJ=C(AB)=(CA)B=JB,
\]

so \(b=c=r\). Taking row sums in \(BC=J\) gives \(r^2=k\).
Consequently

\[
 \boxed{|M|=k+m=2r^2.}
\]

Also \(AJ=A(BC)=(AB)C=JC\) and
\(JA=(BC)A=B(CA)=BJ\), so \(A\) has row and column sum \(r\).
The **whole** adjacency matrix is not regular: its row sums are \(2r\)
on \(L\) and \(r\) on \(H\). Confusing blockwise regularity with
regularity of the whole graph would invalidate this argument.

This completes the restricted matrix argument proposed by José Brox in the
discussion. It does not turn the proposed partition into a general theorem.

## 3. Constant rows: the canonical translation has period dividing ten

Suppose there are elements \(0,1\) satisfying

\[
 0*x=x*0=1\qquad\text{for every }x. \tag{C}
\]

The symbols are distinguished elements, not numerical values. No finiteness
or distinctness assumption is made. We call this the *constant-row/column
case*. Such a pair is unique: two possible lower constants give the same
upper constant by multiplying them together, and that upper constant squares
to the lower constant.

In fact **a constant row alone suffices**. If only \(0*x=1\) is assumed,
(W) gives \(1*1=0\) and \(1*(x*1)=x\), so right multiplication by
\(1\) is injective. Again (W) gives \((y*0)*1=0=1*1\), and
injectivity gives \(y*0=1\). Thus (C) follows. By duality the same is true
of a constant column alone.

Put \(T(x)=x*1\). Identity (W), first with \(x=y=z=0\), gives
\(1*1=0\). With \(y=0\) it gives
\(1*(x*1)=x\); with \(y=z=1\) it gives \((1*x)*1=x\).
Therefore \(T\) is a bijection with

\[
 T^{-1}(x)=1*x,\qquad T0=1,\quad T1=0. \tag{2}
\]

Here are three elementary identities that drive the proof:

\[
 (Ty*x)*(x*y)=x. \tag{3}
\]

\[
 T^3x*x=1. \tag{4}
\]

\[
 a*b=1\quad\Longrightarrow\quad
 \begin{cases}
 b*(z*a)=Tb,\\
 (b*z)*a=T^{-1}a.
 \end{cases} \tag{5}
\]

For (3), take \(z=1\) in (D). For (4), take
\((x,y,z)=(1,T^2x,1)\) in (W) and use (2). For (5), apply (W)
with its middle variable \(a\) and left-hand side \(b\), or apply
(D) with its middle variable \(b\) and left-hand side \(a\), then
cancel \(T^{-1}\) or \(T\), respectively.

We first claim

\[
 x*T^7x=1. \tag{6}
\]

Set \(w=x*T^7x\). Since \(T^3x*x=1\), the second part of (5)
gives \(w*T^3x=T^2x\). Since \(T^7x*T^4x=1\), its first part
gives \(T^4x*w=T^5x\). Now (3), with \(x=w,y=T^3x\), yields

\[
 w=(T^4x*w)*(w*T^3x)=T^5x*T^2x=1,
\]

where the final equality is (4) at \(T^2x\).

Apply (3) with \(y=T^7x\), and use (6):

\[
 (T^8x*x)*1=x,\qquad T^8x*x=T^{-1}x.
\]

Apply (3) with its left-hand side \(T^8x\) and middle variable \(x\).
Using (6) at \(Tx\) gives

\[
 1*(T^8x*x)=T^8x,\qquad T^8x*x=T^9x.
\]

Thus \(T^9x=T^{-1}x\), and finally

\[
 \boxed{T^{10}x=x.} \tag{7}
\]

This is an identity for **all** models satisfying (C), including infinite
ones. Period ten is forced by the equations, not just observed in the
32-element example. Vampire suggested the conclusion; the argument above
extracts it into a short proof using only (W), (D), and (C).

## 4. Classification of the constant-row/column case

### 4.1 The two equational lemmas

We use two lemmas. Their complete equational derivations, including exact
inputs and every rewrite, are in the
[proof appendix](1485_spectrum_equational_proofs.md).

**Translation lemma.** Under (W) and (C),

\[
 T^2(x*y)=T^2x*T^2y. \tag{8}
\]

Together with (2), this says that \(T^2\) is an automorphism. Andy Jiang
had already obtained this lemma in the discussion; the appendix supplies a
fresh reproducible derivation. It does not use (7).

**Central-constant lemma.** Under (W), (C), and
\(1*x=x*1\) for every \(x\), the operation is commutative.

The appendix input includes two convenient consequences rather than making
the prover rediscover them. The inverse identity is (2). To obtain the square
identity, put \((y,z)=(1,0)\) in (W). Centrality gives
\(Tx*Tx=x\), and \(T=T^{-1}\) gives, after replacing \(x\) by
\(Tx\),

\[
 x*x=Tx=1*x. \tag{9}
\]

Thus the appendix's `inv` and `square` assumptions have already been proved.
No appeal to finiteness, Boolean structure, or commutativity is hidden in
these inputs. These two lemmas are the machine-assisted equational portion
of the argument; they have not been imported as unchecked Lean axioms.

### 4.2 Untwisting

Let \(\sigma=T^6\). By (8), it is an automorphism, and by (7),
\(\sigma^5=T^{30}=\mathrm{id}\). Both \(0\) and \(1\) are
fixed by \(\sigma\). Define

\[
 x\circ y=\sigma^{-1}x*\sigma y=T^{-6}x*T^6y. \tag{10}
\]

Twisting an E1485 magma by mutually inverse automorphisms of order dividing
five preserves (W). Explicitly, for \(x\diamond y=Ax*A^{-1}y\),

\[
 (y\diamond x)\diamond(x\diamond(z\diamond y))
 =(A^2y*x)*(x*(A^{-1}z*A^{-3}y))=x,
\]

since \(A^2=A^{-3}\). Use \(A=\sigma^{-1}\) for (10).
The constant-row identities also remain valid. Moreover,

\[
 x\circ1=T^{-5}x=T^5x=1\circ x.
\]

The central-constant lemma therefore makes \(\circ\) commutative.

### 4.3 Recovering a Boolean algebra

Here is an explicit link to a standard single axiom, so that “Boolean” is
not merely suggested by the examples. Work temporarily with \(\circ\)
and put \(n(x)=x\circ1=1\circ x\). From (D) with its final variable
\(0\),

\[
 n(x)\circ(x\circ y)=x.
\]

Another use of (D) gives

\[
 \begin{aligned}
 x\circ((x\circ y)\circ x)
 &=((x\circ1)\circ(x\circ y))\circ((x\circ y)\circ x)\\
 &=x\circ y.
 \end{aligned} \tag{11}
\]

Consequently, commutativity and (11) give
\(y\circ((x\circ y)\circ y)=y\circ x\). Substituting this
into (W) yields

\[
 (y\circ((x\circ y)\circ y))\circ(x\circ(z\circ y))=x.
\]

This is McCune et al.'s single axiom for Boolean NAND, equation 345169 in
the project. Its equivalence with Boolean algebra is formalized in
[Sheffer.lean](../equational_theories/Sheffer.lean) and
[ShefferAlgebra.lean](../equational_theories/ShefferAlgebra.lean).
Thus \(\circ\) is the NAND operation of a Boolean algebra on the same
carrier. Its Boolean operations are term-defined from \(\circ\), so
\(\sigma\), which remains an automorphism of \(\circ\), is also a
Boolean-algebra automorphism.

Solving (10) for the original operation proves the classification:

\[
 \boxed{x*y=\neg(\sigma x\wedge\sigma^{-1}y),
 \qquad \sigma^5=\mathrm{id}.} \tag{12}
\]

Conversely, every Boolean algebra with such an automorphism gives a model
of (W) and (C), by the same twisting calculation. Hence this is an exact
description of the entire constant-row/column class, not just a construction
inside it.

### 4.4 Finite consequences

A finite Boolean algebra with \(m\) atoms has \(2^m\) elements. Its
automorphism \(\sigma\) permutes the atoms in cycles of length one or
five. Splitting the atom set into those cycles shows that every finite
constant-row/column model is a direct product of copies of:

- the two-element NAND magma;
- the 32-element cyclically twisted NAND magma.

In particular its order is \(2^{a+5b}\), hence a square or twice a square.
Every power of two occurs, by untwisted NAND. Since \(0,1,T\), and hence
\(\sigma\) and \(\circ\), are recoverable from the original magma,
isomorphisms preserve this description. There are exactly
\(\lfloor m/5\rfloor+1\) isomorphism classes of constant-row/column
models of order \(2^m\), one for each possible number of five-cycles.

The smallest noncommutative finite model in this class therefore has order
32. To see that a nontrivial twist really is noncommutative, centrality of
the upper constant would imply \(T=T^{-1}\), hence \(T^2=\mathrm{id}\)
and \(\sigma=T^6=\mathrm{id}\).

## 5. Why this still does not prove the full conjecture

There are two distinct restrictions in the results above, and neither can
be silently removed.

The high/low family in §2 does not contain the cyclically twisted
32-element example. In fact that example has no homomorphism onto NAND of
order two. Any such surjection would preserve \(0,1\), hence the
recoverable Boolean operations and the twist. A Boolean homomorphism from
the five-atom Boolean algebra to the two-element algebra selects an atom;
compatibility with the five-cycle would require a fixed atom. There is none.
Thus the proposed general “noncentral implies a two-element quotient”
reduction is false.

The constant-row/column classification in §4 does not cover even all known
models of order eight. For example, the following table, supplied by Kevin M
in the discussion, satisfies (W) but has no constant row:

```text
1 0 0 1 2 2 3 3
0 0 0 0 3 3 3 3
4 4 5 4 5 5 4 5
7 4 5 7 6 6 4 5
1 0 0 1 6 6 3 3
7 4 5 7 2 2 4 5
4 4 5 4 5 5 4 5
0 0 0 0 3 3 3 3
```

It does lie in §2's family: take \(L=\{0,3,4,5\}\) and
\(H=\{1,2,6,7\}\). The two partial converse results are complementary,
not a claim that the constant-row classification covers the smaller examples.

This also blocks one tempting shortcut in the involutive-squaring case.
Define \(p(x,y)=(y*x)*(x*y)\). For central groupoids this is the first
projection, and for NAND it is meet, but it need not be associative even
when \((x*x)*(x*x)=x\). In the displayed table,

\[
 p(p(3,0),2)=6\ne2=p(3,p(0,2)).
\]

So a semilattice decomposition cannot simply assume associativity of this
term operation.

The next structural target is a justified reduction of general finite
models to Boolean-like quotients and square-sized pieces, accommodating the
non-product examples. The constant-row classification identifies the possible
Boolean/twisted building blocks, but it does not yet supply that reduction
or any uniformity theorem for its hypothetical fibers. Likewise, the
discussion's conjecture that all nonempty fibers of a fixed left or right
translation have the same size is not used as a theorem here.

## Validation

Both appendix derivations reproduce byte-for-byte with Twee 2.4.2 and
`--quiet --all-lemmas`: **0.332 s** for the translation lemma and **1.418 s**
for the central-constant lemma, measured as total subprocess times. A separate
substitution/congruence check of the final traces verified all **81 derived
identities/goals and 222 rewrites**, using only each trace's stated axioms and
previously established identities. This is independent checking of the
equational steps, not Lean kernel verification or a check of the entire
mathematical exposition.

Direct evaluation also verified (W), involutive squaring, and the two
high/low hypotheses for the displayed order-eight table. For the explicit
twisted Boolean representatives with zero through five atoms, it verified
(W), \(T^{10}=\mathrm{id}\), \(T^6=\sigma\), and the untwisting
formula on every argument tuple. These are checks of the displayed
constructions, **not** an exhaustive search through all magmas of those
orders. Local document links and whitespace checks pass. No Lean source was
changed or rebuilt for this mathematical research pass.

## Sources and attribution

The supplied `/home/alex_harmonic_fun/1485_log.pdf` contains the late-October
to mid-November 2024 discussion. Much ordinary text is stored as graphical
outlines, so the matching public archive was used for searchable text, with
rendered PDF pages checked against it. Important archive entries:

- [Kevin M's non-product order-eight example](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/1485.html#478294093).
- [Tao's high/low graph construction](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/1485.html#478847118).
- [Jiang: squared translation is an automorphism](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/1485.html#479985725).
- [Jiang: the 32-element model and failed two-element-quotient conjecture](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/1485.html#480045734).
- [Le Floch's subset interpretation of that model](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/1485.html#480128244).
- [Tao's order-five twisting construction](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/1485.html#480186232).
- [Le Floch's equal-fiber conjecture](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/1485.html#480626377).
- [Brox's block-matrix argument](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/1485.html#480719939), followed by [Jiang's warning about the 32-element model](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/1485.html#480721979).

This record distinguishes results derived in this investigation from facts
already present in the discussion; it does not assert a literature-wide
novelty claim for the period-ten identity or the constant-row classification.
