# The finite spectrum of E1480

**Status:** fully formalized in Lean, 2026-09-23. The exact theorems are
`Spectrum.spectrum_1480`, `Spectrum.Catalogue.exact_1480`, and
`Spectrum.Catalogue.exact_2089`. The all-orders existence theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`, with no native checks.
The exact spectra add the two existing native-checked finite exclusions.

The spectrum of

\[
 x=(y\diamond x)\diamond\bigl(x\diamond(x\diamond z)\bigr)
\]

is exactly \(\mathbb N_{>0}\setminus\{2,3\}\). The constructions below give
orders 4+2m and 5+2m for every nonnegative m. The singleton is automatic;
the existing Lean exclusions rule out 2 and 3.

## Even orders

Start with four points 0,1,2,3 and add two points A_i,B_i for each i in an
arbitrary set I. On the core use the table

```
    0 1 2 3
0   3 3 2 2
1   1 1 0 2
2   3 3 2 2
3   1 1 0 0
```

The core-to-new products, listing core elements in order, are

\[
(0,1,2,3)\diamond A_i=(2,1,2,1),\qquad c\diamond B_i=A_i.
\]

Both new points have the same products with the core:

\[
A_i\diamond(0,1,2,3)=B_i\diamond(0,1,2,3)=(B_i,3,0,B_i).
\]

For new-to-new products use

\[
\begin{array}{c|cc}
 & i=j & i\ne j\\\hline
A_i\diamond A_j &3&B_i\\
B_i\diamond A_j &1&B_i\\
A_i\diamond B_j &B_i&A_j\\
B_i\diamond B_j &B_i&A_j
\end{array}
\]

## Odd orders

Start with five points 0,1,2,3,4 and again add A_i,B_i for each i in I.
The core is

```
    0 1 2 3 4
0   4 4 4 3 3
1   2 1 1 0 2
2   4 4 4 0 0
3   2 4 4 3 3
4   2 1 1 0 2
```

Set

\[
(0,1,2,3,4)\diamond A_i=(3,1,0,4,1),\qquad c\diamond B_i=A_i,
\]

and

\[
A_i\diamond(0,1,2,3,4)=B_i\diamond(0,1,2,3,4)=(B_i,4,4,0,B_i).
\]

The remaining rules are

\[
\begin{array}{c|cc}
 & i=j & i\ne j\\\hline
A_i\diamond A_j &4&B_i\\
B_i\diamond A_j &0&0\\
A_i\diamond B_j &B_i&A_j\\
B_i\diamond B_j &B_i&A_j
\end{array}
\]

## Verification and all-orders conclusion

Each operation uses only equality of indices and returns either a core point or
a point whose index occurs in an input. Consequently it commutes with every
injective relabeling of the indices.

To verify E1480 on any x,y,z, collect the at most three indices that occur in
these elements. Every intermediate product stays in this core-plus-indices
subalgebra. Embed its index set into {0,1,2}. Injectivity preserves every branch
of the formulas, so the identity reduces to the case of three indices. Direct
substitution in the displayed rules verifies all 10 cubed even-family cases
and all 11 cubed odd-family cases. This is a finite verification of a universal
construction, independent of the size of I, including infinite I.

The formulas were also checked independently in Python for every m from 0
through 15, giving every order from 4 through 35. Lean verifies the general
formulas by cases on the core/new arguments and index equalities.

Taking I of size m gives 4+2m and 5+2m. These include every integer at least
four, completing the spectrum with the singleton and the two exclusions.

The [construction file](../equational_theories/Spectrum/Equation1480Construction.lean)
proves the identities for arbitrary index types, including infinite ones, by
cases on core points, pair types, and index equalities. No finite-model search
or SAT certificate is assumed in these existence proofs.
The [spectrum file](../equational_theories/Spectrum/Equation1480.lean) combines
the even and odd constructions with the singleton and the two exclusions.
