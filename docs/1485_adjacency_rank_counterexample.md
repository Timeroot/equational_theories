# Ordinary adjacency can have rank larger than the maximum degree

Research note, 18 September 2026. The proposed equality
`rank(A)=s`, for ordinary adjacency `A` and maximum translation
degree `s`, is false even with a full central core. The lower bound
`rank(A)≥s` is not contradicted.

## An order-eight example

Use elements `0,...,7` and the following multiplication table:

```text
1 0 0 1 2 2 3 3
0 0 0 0 3 3 3 3
4 4 4 5 5 4 5 5
6 4 4 6 7 7 5 5
1 0 0 1 2 2 5 5
6 4 4 6 7 7 3 3
0 0 0 0 3 3 3 3
4 4 4 5 5 4 5 5
```

This is zero-based table number 2 in Kevin M's `n8_unique.txt`
archive, also used in [the mixed-projection note](1485_image_research.md).
Direct substitution verifies all 512 instances of E1485. Its degree
vector is `(4,2,2,4,4,4,2,2)`, and its central set is
`{1,2,6,7}`. Thus `r=2`, `s=4`, and the central core is full.

Its ordinary adjacency matrix is

\[
A=\begin{pmatrix}
1&1&1&1&0&0&0&0\\
1&0&0&1&0&0&0&0\\
0&0&0&0&1&1&0&0\\
0&0&0&0&1&1&1&1\\
1&1&1&0&0&1&0&0\\
0&0&0&1&1&0&1&1\\
1&0&0&1&0&0&0&0\\
0&0&0&0&1&1&0&0
\end{pmatrix}.
\]

Rows `6,7` repeat rows `1,2`, and row `5` is row `0` plus
row `3` minus row `4`. Hence the rank is at most five. The minor
on rows `(0,1,2,3,4)` and columns `(0,1,3,4,6)` is

\[
\begin{pmatrix}
1&1&1&0&0\\
1&0&1&0&0\\
0&0&0&1&0\\
0&0&0&1&1\\
1&1&0&0&0
\end{pmatrix},
\]

whose determinant is one. Therefore

\[
\boxed{\operatorname{rank}(A)=5>4=s.}
\]

The row relations and determinant also prove rank five over every
field, not just over the rationals.

## Unimodular coordinate blocks need not align

Take the central vertex `h=6`. Its two top successors are `0,3`
and its two top predecessors are `3,5`. Use row blocks

\[
\operatorname{Row}(0)=(0,1,2,3),\qquad
\operatorname{Row}(3)=(4,5,6,7),
\]

and column blocks

\[
\operatorname{Col}(3)=(0,1,5,6),\qquad
\operatorname{Col}(5)=(2,3,4,7).
\]

Write the resulting block matrix as `[[A₀₀,A₀₁],[A₁₀,A₁₁]]`.
The four block determinants are respectively `−1,1,−1,1`.
Nevertheless,

\[
A_{11}-A_{10}A_{00}^{-1}A_{01}
=\begin{pmatrix}
0&-1&-1&0\\
0&1&1&0\\
0&0&0&0\\
0&0&0&0
\end{pmatrix}\ne0.
\]

Thus even full core and unimodularity of every central-coordinate
block do not force a vanishing Schur complement or an upper rank
bound of `s`.

The table was checked with the complete finite-table regression routine
in `scripts/1485_structure_check.py`; the rank certificate above is
exact and independent of numerical rank tolerances. No general upper
rank assertion is made here.
