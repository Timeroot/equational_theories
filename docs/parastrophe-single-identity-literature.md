# Compressing division-image bases to a single identity

Literature review, 2026-11-02. These are research notes, not new Lean results.
In particular, this review does not settle the E714 or E872 image questions.

The relevant terminology is **one-based equational theory**: the entire theory
has a basis consisting of one identity, in the specified operation signature.
This is stronger than having one additional axiom relative to an ambient class
of quasigroups. Our `SingleEquation` question requires a characterization among
all magmas, including the appropriate bijectivity as a consequence.

## There is no unconditional compression theorem

Even the two magma identities

```
x*x = x
x*y = y*x
```

cannot be replaced by one identity. This remains true if only finite magmas
are considered. Here is an elementary argument, independent of the references:

1. If both sides of a proposed identity are composite terms, the two-element
   constant-operation magma satisfies it, but is not idempotent.
2. Otherwise one side is a variable, say `x=t`. The two-element join semilattice
   must satisfy this identity. Evaluation in that semilattice forces the set
   of variables occurring in `t` to be exactly `{x}`.
3. Every idempotent magma satisfies every identity `x=t(x)`. In particular, the
   two-element left-projection magma satisfies it, but is not commutative.

All the countermodels used here have two elements. Allowing a longer identity
or more variables does not avoid the obstruction.

For another example, associativity and commutativity cannot be combined into
one magma identity. Keith Kearnes discusses this obstruction, and a stronger
failure of meets and joins in the ordering of single magma identities, in his
[MathOverflow answer](https://mathoverflow.net/a/482742).

## Positive theorems with additional hypotheses

### Groups in the division signature

Graham Higman and B. H. Neumann, *Groups as groupoids with one law*,
Publicationes Mathematicae Debrecen 2 (1952), 215–221,
[DOI](https://doi.org/10.5486/PMD.1952.2.3-4.10).

Every finitely based equational theory of groups, presented with the single
operation `x*y = x y⁻¹`, is one-based. This includes adding finitely many
identities to group theory and compressing the resulting whole theory.

The accessible source checked for this statement and the generalizations is
George F. McNulty, *Minimum bases for equational theories of groups and rings:
the work of Alfred Tarski and Thomas Green*, Annals of Pure and Applied Logic
127 (2004), 131–153,
[author's PDF](https://people.math.sc.edu/mcnulty/preprints/elsbase.pdf),
[DOI](https://doi.org/10.1016/j.apal.2003.11.012).

Tarski's Theorem 5 there is a more general compression mechanism. Write `-`
for a basic binary operation and suppose a finitely based theory T contains

```
ε:  y = ((z-z)-(x-y))-((w-w)-x).
```

If a nonempty set Γ of identities of T, together with ε, implies a substitution
instance of every identity in a finite basis for T, then T has a basis of size
at most |Γ|. Corollary 12 gives a bound `max(1,n-1)` when every model of T has a
one-element subalgebra and n is the number of basic operation symbols. In
particular, this is one identity when n=1.

Theorem 3 gives the exact minimum `max(1,n-1)` for nontrivial finitely based
theories term equivalent to group theories in n operation symbols. Thus the
choice of signature is substantive, even for groups. One must not assume that
introducing division, proving a single axiom in the new language, and replacing
its symbols automatically recovers the intended original magma theory.

### Distributive and permutable congruences

R. Padmanabhan and R. W. Quackenbush, *Equational theories of algebras with
distributive congruences*, Proceedings of the AMS 41 (1973), 373–377,
[DOI](https://doi.org/10.1090/S0002-9939-1973-0325498-2).

Every finitely based variety with both distributive and permutable congruences
is one-based. These are the arithmetical varieties; equivalently they have a
Pixley term. This statement is given in the publisher's abstract and is also
reported in McNulty's survey. The full 1973 PDF was not accessible in this
review.

William McCune and R. Padmanabhan's *Automated Deduction in Equational Logic
and Cubic Curves* (1996) provides a concrete related reduction schema:

```
p(p(x,x,y), p(f(z),u,z), z) = y.
```

This forces the Pixley identities
`p(x,x,y)=y`, `p(x,y,y)=x`, `p(x,y,x)=x`, and `f(x)=x`.
See the authors' [PIX-2 proof input](https://www.cs.unm.edu/~mccune/papers/monograph/probs/PIX-2/f1.in).
This is a useful template, but it does not supply a Pixley term in an arbitrary
quasigroup variety.

### A warning about minority and Mal'tsev terms

R. Padmanabhan and B. Wolk, *Equational theories with a minority polynomial*,
Proceedings of the AMS 83 (1981), 238–242,
[DOI](https://doi.org/10.1090/S0002-9939-1981-0624905-X).

The paper states both:

* Every finitely based variety of type ⟨3⟩ satisfying the two-thirds minority
  condition is one-based. Type ⟨3⟩ means **one basic ternary operation**.
* For every natural number n there is a variety admitting a full minority term
  which is `(n+1)`-based but not n-based.

Consequently, merely producing a minority term, or a Mal'tsev term, is not a
general single-axiom theorem. The positive statement's signature restriction
cannot be dropped.

**Full-text follow-up, 4 November:** the five-page paper was retrieved and read
from the [publisher's PDF](https://www.ams.org/journals/proc/1981-083-02/S0002-9939-1981-0624905-X/S0002-9939-1981-0624905-X.pdf?download=1).
Theorem 1 gives a concrete construction. First compress the extra identities,
relative to the Mal'tsev laws, to `f(dummy variables,w)=w`. Its single defining
identity is

```
f₀(p(f₁(p(x,x,y)), f₂(p(z,z,f₃(w))), w)) = y.
```

The subscripts denote copies of the same term with independent dummy variables,
not new operation symbols. The proof first recovers `p(x,x,y)=y`. A crucial
subsequent step identifies dummy variables and uses idempotency repeatedly to
reduce copies of f to the identity. This is justified because **f is built only
from p**. Replacing p by an arbitrary magma Mal'tsev term while letting f also
use the original multiplication does not justify that step: idempotency of p
does not imply idempotency of multiplication.

The negative construction in Theorem 2 has signature `(3,1,…,1)`: a basic
minority operation and n basic unary operations required to be the identity.
Over F₂, translate these n+1 operations independently. Each valid identity
imposes at most one homogeneous linear constraint on the n+1 translation
parameters, so n identities cannot exclude every unwanted translation.
This confirms the signature obstruction without claiming a binary-only
counterexample or settling any of our remaining division-image fields.

For additional perspective, Douglas D. Smith's
[*Non-recursiveness of the set of finite sets of equations whose theories are
one-based*](https://doi.org/10.1305/ndjfl/1093894637) (1972) proves undecidability
already for finite presentations in a signature with two binary operations and
two constants. This does not assert undecidability for our restricted catalogue.

## Applicability to our two main compression problems

### E714 left division

The image is E464 plus left bijectivity. Define

```
F_y(x) = y*(x*(x*(x*y)))
G_y(x) = (y*x)*((y*x)*((y*x)*y)).
```

An exact two-identity basis is `F_y(x)=x` and `G_y(x)=x`: these give the two
inverse identities for the row maps. In E464, left and right bijectivity are
equivalent, so this image consists of quasigroups.

Two small members obstruct direct use of the positive theorems above:

* Addition on the vector space F₂² satisfies both identities. Its congruences
  are its additive subspaces, including the three distinct one-dimensional
  subspaces. Their lattice is M₃, which is not distributive. Thus this image
  variety is not arithmetical and has no Pixley term.
* On F₃, `x*y=-x-y` satisfies both identities and is idempotent. Tarski's ε
  forces a constant diagonal (`x-x=y-y`, Lemma 7 of the survey), so ε fails in
  this nontrivial example. Every magma term is idempotent in an idempotent
  magma, so interpreting ε's binary operation by a magma term does not fix
  this particular obstruction.

Neither argument says that this image is not one-based. They show why these
general sufficient conditions do not directly settle it. The existing
nine-element countermodel to `F_y(G_z(x))=x` remains an obstruction to that
specific proposed compression, not to every single identity; see
[`Equation714ImageCandidate.lean`](../equational_theories/Parastrophes/Equation714ImageCandidate.lean).

### E872 left division

With `c(x)=x*((x*x)*x)`, the exact finite basis is

```
x = x*c(x)
x = y*(c(x)*(y*x)).
```

On arbitrary carriers, append

```
c(x*y)*(x*(x*y)) = y.
```

These statements are formalized in
[`Equation872ImageBasis.lean`](../equational_theories/Parastrophes/Equation872ImageBasis.lean).

The nontrivial right-projection magma `x*y=y` satisfies the entire three-law
basis. It has bijective rows but constant columns. Every term in this magma
is a projection, so no common Mal'tsev, minority, majority, or Pixley term
exists for the whole image class. Tarski's ε also fails: its right-hand side
evaluates to x, although its left-hand side is y. Thus the group-division and
arithmetical-variety theorems do not resolve this image either.

## Consequences for further work

These references supply genuine compression tools, but no blanket theorem
found in this review settles the remaining exact image bases. A candidate
application must establish its hypotheses for the **whole image class**, and
its final identity must force membership among all target magmas, not just
among quasigroups assumed in advance. An arbitrary-carrier compression also
settles the corresponding finite question; the absence of an applicable
arbitrary-carrier theorem says nothing negative about finite-only compression.
