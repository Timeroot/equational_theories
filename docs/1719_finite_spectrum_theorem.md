# The finite spectrum of E1719

**Status:** fully formalized in Lean, 2026-09-23. The exact theorems are
`Spectrum.spectrum_1719`, `Spectrum.Catalogue.exact_1719`, and
`Spectrum.Catalogue.exact_1888`. Their proofs use only `propext`,
`Classical.choice`, and `Quot.sound`; there are no native-check dependencies.

The original paper proof below uses Shen Hao's incomplete-design theorem.
The Lean proof replaces that existence input with an explicit Bose construction,
described in Section 6, built from the existing idempotent Latin squares.

## Theorem

A nonempty finite magma satisfying

\[
\tag{E1719}
x=(y\mathbin{\diamond}y)\mathbin{\diamond}
       ((x\mathbin{\diamond}x)\mathbin{\diamond}y)
\]

exists on exactly the following positive cardinalities:

\[
\boxed{\operatorname{Spec}_{\mathrm{fin}}(E1719)
       =\mathbb Z_{\geq 1}\setminus\{2\}.}
\]

The same spectrum follows for the dual law E1888 by reversing multiplication.
The convention here excludes the empty magma from the spectrum.

## 1. A twisting lemma

Let \((Q,*)\) satisfy the semisymmetric identity

\[
\tag{1} y*(x*y)=x.
\]

Suppose \(S\) is a permutation of \(Q\) such that

\[
\tag{2} S^3=\mathrm{id},\qquad S^2(x)*x=S(x)\quad(x\in Q).
\]

Powers of \(S\) mean composition. Define

\[
\tag{3} x\diamond y=S^2(x)*y.
\]

Then \(x\diamond x=S(x)\), and

\[
\begin{aligned}
(y\diamond y)\diamond((x\diamond x)\diamond y)
 &=S(y)\diamond(S(x)\diamond y)\\
 &=S^2(S(y))*\bigl(S^2(S(x))*y\bigr)\\
 &=y*(x*y)=x.
\end{aligned}
\]

Thus (3) satisfies E1719. No compatibility of \(S\) with multiplication,
such as being an automorphism, is required.

There is also a converse, which explains the construction. In an E1719
magma put \(S(x)=x\diamond x\). Substituting \(y=S(x)\) into E1719 gives

\[
x=S^2(x)\diamond S^2(x)=S^3(x).
\]

Hence \(S\) is a permutation of order dividing three. Define
\(x*y=S(x)\diamond y\). Then

\[
y*(x*y)=S(y)\diamond(S(x)\diamond y)=x,
\qquad S^2(x)*x=x\diamond x=S(x).
\]

Consequently (1)–(3) describe precisely the twisting data needed for E1719.

## 2. The design-existence theorem

An incomplete Mendelsohn triple system \(\operatorname{IMTS}(v,w;1)\)
consists of a set \(V\) of size \(v\), a hole \(H\subseteq V\) of size
\(w\), and cyclically ordered triples of distinct points. Every ordered pair
of distinct points not both in \(H\) occurs in exactly one triple as a
consecutive pair; no ordered pair of hole points occurs. A cyclic triple
\((a,b,c)\) contains the ordered pairs \((a,b),(b,c),(c,a)\).

We use the following specialization of Shen's existence theorem:

> For positive integers \(v,w\), with \(v\geq 2w+1\), an
> \(\operatorname{IMTS}(v,w;1)\) exists if and only if
> \[
> (v-w)(v-2w-1)\equiv0\pmod3
> \]
> and \((v,w)\ne(6,1)\).

Reference: **Shen Hao**, “On the embeddings of mendelsohn triple systems,”
*Acta Mathematica Sinica*, **9** (1993), no. 3, 246–251,
[doi:10.1007/BF02582902](https://doi.org/10.1007/BF02582902).
The full index-\(\lambda\) existence criterion, including the exceptional
triple \((6,1,1)\), is stated in the
[publisher's public abstract](https://link.springer.com/article/10.1007/BF02582902),
which was checked for this draft. We only use \(\lambda=1\).

For comparison, the displayed congruence is equivalent to the usual ordered-pair
count \(v(v-1)-w(w-1)\equiv0\pmod3\), because their difference is
\(-3w(v-w)\).

The two consequences needed here are:

- \(\operatorname{IMTS}(n,1;1)\) exists for every
  \(n\geq3\) with \(n\equiv0,1\pmod3\), except \(n=6\).
- \(\operatorname{IMTS}(n,2;1)\) exists for every
  \(n\geq5\) with \(n\equiv2\pmod3\).

Indeed, the two congruences are respectively
\((n-1)(n-3)\equiv0\pmod3\) and
\((n-2)(n-5)\equiv0\pmod3\). The size inequalities are respectively
\(n\geq3\) and \(n\geq5\), and the stated exception does not concern a
two-point hole.

## 3. From incomplete systems to E1719 models

Given an incomplete Mendelsohn triple system, each cyclic triple \((a,b,c)\)
defines

\[
a*b=c,\qquad b*c=a,\qquad c*a=b.
\]

These prescriptions define every product of distinct points not both in the
hole. Set \(x*x=x\) outside the hole. Fill the hole with any semisymmetric
operation. The resulting operation on \(V\) is semisymmetric: (1) follows
from cyclic rotation for each triple, from idempotence for an outside diagonal,
and from the chosen operation for pairs inside the hole. These cases exhaust
all ordered pairs.

### A one-point hole

Fill the hole \(\{a\}\) by \(a*a=a\). The resulting semisymmetric operation
is idempotent everywhere. Take \(S=\mathrm{id}\) in the twisting lemma.
This supplies all orders \(n\geq3\) congruent to 0 or 1 modulo 3, except 6.

### A two-point hole

Write the hole as \(\{a,b\}\), and fill it with the addition table of the
cyclic group of order two:

\[
\begin{array}{c|cc}
 *&a&b\\\hline
 a&a&b\\
 b&b&a
\end{array}
\]

This is semisymmetric. After filling, \(b\) is the only point for which
\(x*x\ne x\).

Choose any \(c\notin\{a,b\}\), and let \((b,c,d)\) be the unique cyclic
triple containing the ordered pair \((b,c)\). Its third point \(d\) is
distinct from \(b,c\), and \(d\notin\{a,b\}\): a triple containing two
hole points would contain a forbidden ordered pair of hole points.

Let \(S\) be the cycle

\[
\tag{4} b\longmapsto c\longmapsto d\longmapsto b,
\]

fixing all other points. Then \(S^3=\mathrm{id}\). The compatibility in
(2) follows on the three moved points from

\[
d*b=c,\qquad b*c=d,\qquad c*d=b.
\]

Every fixed point \(x\) is different from \(b\), so
\(S^2(x)*x=x*x=x=S(x)\) there as well. The twisting lemma therefore supplies
an E1719 model on exactly \(n\) points.

Shen's theorem now gives every order \(n\equiv2\pmod3\) with \(n\geq5\).
In particular, this gives all orders in the previously missing residue class.

## 4. The remaining orders 1 and 6

Order 1 is immediate.

For order 6, define a semisymmetric operation on \(\{0,1,2,3,4,5\}\) by
cyclic triples. Include the three singleton prescriptions

\[
(0,0,0),\quad(1,1,1),\quad(2,2,2),
\]

and the following eleven cyclic prescriptions:

\[
\begin{gathered}
(0,1,4),\ (0,2,5),\ (0,3,2),\ (0,4,3),\ (0,5,1),\\
(1,2,3),\ (1,3,4),\ (1,5,2),\\
(2,4,4),\ (3,3,5),\ (4,5,5).
\end{gathered}
\]

Here repetitions within a triple are allowed: for example, \((2,4,4)\)
means \(2*4=4\), \(4*4=2\), and \(4*2=4\). The prescriptions are
disjoint and cover every ordered pair: the singleton triples contribute three
pairs and the other eleven contribute three pairs each, totaling 36. For
convenience, the resulting complete table is

\[
\begin{array}{c|rrrrrr}
 *&0&1&2&3&4&5\\\hline
 0&0&4&5&2&3&1\\
 1&5&1&3&4&0&2\\
 2&3&5&2&1&4&0\\
 3&4&2&0&5&1&3\\
 4&1&3&4&0&2&5\\
 5&2&0&1&3&5&4
\end{array}
\]

Cyclic closure of the prescriptions proves (1). Take

\[
S=(0\ 2\ 5)(1\ 3\ 4).
\]

Both three-cycles are among the displayed cyclic prescriptions, so
\(S^2(x)*x=S(x)\) for every point. The twisting lemma again gives E1719.
This is an explicit finite certificate, independent of any existence theorem
for order six.

## 5. Exclusion of order 2 and conclusion

As shown in Section 1, the squaring map of any E1719 magma satisfies
\(S^3=\mathrm{id}\). On a two-point set this forces \(S=\mathrm{id}\),
since the only other permutation is a transposition. Thus an order-two model
would be idempotent and would satisfy

\[
x=y\diamond(x\diamond y).
\]

Let its distinct elements be \(a,b\). If \(a\diamond b=b\), this identity
gives \(a=b\diamond b=b\), a contradiction. Hence \(a\diamond b=a\).
The same identity gives \(b\diamond a=a\). Interchanging \(a,b\) now gives

\[
b=a\diamond(b\diamond a)=a\diamond a=a,
\]

again a contradiction. No two-element model exists.

Sections 3 and 4 provide every other positive order, proving the theorem.

## 6. Constructive existence used in Lean

Only the two-point-hole case needs a new construction: the ordinary Mendelsohn
models for the other residue classes are already formalized in `Equation66.lean`.

Let \((Q,\circ)\) be an idempotent Latin square of positive order \(m\).
Such a square exists for every \(m\ne2\), by the explicit odd-order and
prolongation constructions in `IdempotentLatin.lean`. Write \(a\backslash b\)
for the solution of \(a\circ u=b\), and \(b/a\) for the solution of
\(u\circ a=b\).

Use the carrier

\[
\{A,B\}\;\sqcup\;(Q\times\mathbb Z/3\mathbb Z).
\]

For each \(q\in Q\), put a copy of the following five-point semisymmetric
operation on \(A,B,(q,0),(q,1),(q,2)\), labeled respectively \(0,1,2,3,4\):

\[
\begin{array}{c|rrrrr}
 *&0&1&2&3&4\\\hline
 0&0&1&3&4&2\\
 1&1&0&4&2&3\\
 2&4&3&2&0&1\\
 3&2&4&1&3&0\\
 4&3&2&0&1&4
\end{array}
\]

The copies agree on the shared two-point subquasigroup \(\{A,B\}\).
For distinct fibres \(a\ne b\), use the existing Bose cross operation:

\[
(a,i)*(b,j)=
\begin{cases}
(a\circ b,i+1),&j=i,\\
(b/a,i),&j=i+1,\\
(b\backslash a,j),&j=i+2.
\end{cases}
\]

The first coordinate of each output differs from both \(a\) and \(b\),
by idempotence and cancellation in the Latin square. Thus evaluating
\(y*(x*y)\) for points from distinct fibres uses the cross operation twice.
The three displayed cases give \(x\), using respectively right division,
left division, and the defining Latin product identities. Pairs lying in one
five-point copy obey semisymmetry by its table. These cases prove that the
global operation is semisymmetric.

Only \(B\) is non-idempotent. Fix any \(q\in Q\). The table gives the
oriented triangle \((B,(q,0),(q,2))\), so the permutation cycling these three
points and fixing all others satisfies the twisting lemma. This yields an
E1719 model of order \(3m+2\).

This constructs every order congruent to two modulo three except 2 and 8.
The explicit order-eight table is checked by ordinary kernel reduction in
`Generated/NoteWitnesses.lean`, as is the exceptional order-six table.
Together with the existing Mendelsohn constructions, this proves every positive
order except two without using Shen's theorem in Lean.

The implementation is divided into:

- [`Equation1719Twist.lean`](../equational_theories/Spectrum/Equation1719Twist.lean):
  the twisting lemma, its converse, and the three-cycle construction;
- [`MendelsohnTwoHole.lean`](../equational_theories/Spectrum/MendelsohnTwoHole.lean):
  the shared-two-point Bose operation, semisymmetry, and cardinality;
- [`Equation1719.lean`](../equational_theories/Spectrum/Equation1719.lean):
  the order-two exclusion, complete existence theorem, and exact spectrum.

## Verification

The original paper formulas were independently checked in Python, including
all 36 ordered pairs in the order-six certificate. Incomplete systems and their
twists were also checked at orders 3, 4, 5, 7, 8, 11, 14, 17, 20, 23, and 26.
The all-orders Lean proof uses the explicit construction in Section 6.

Each main theorem carries a `spectrum_assert ... complete`. The axiom audit
also pins down the standard axiom list of `Spectrum.spectrum_1719` and checks
that both catalogue entries have zero native-check dependencies.
