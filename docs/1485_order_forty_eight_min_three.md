# Order 48: excluding the minimum-three, least-degree-six branch

Research note, 18 September 2026. This is an analytic finite proof,
not a Lean declaration. It uses no exhaustive incidence enumeration
or SAT conclusion.

**Theorem.** No E1485 magma of order 48 has minimum translation
degree three and least noncentral translation degree six.

This does not exclude order 48 globally: the minimum-degree-four
branch is separate. It also does not address a minimum-three model
in which degree four occurs.

## 1. Reduction to four central and nine top vertices

Minimum degree three gives maximum degree sixteen. Degrees divide
48 and occur together with their complements `48/d`. If six is
the least noncentral degree, the only degrees are

\[
3,6,8,16.
\]

Both middle degrees occur. Write `A,B,T` for their degree-six,
degree-eight, and degree-sixteen classes, respectively.

The central-defect gap and the five-central exclusion leave three,
four, or nine central vertices. Three central vertices force degree
four; nine force full-core order `9·2^j`. Neither is possible here.
Thus there are four central vertices. The top count is nine or ten.
In the [ten-top case](1485_four_central_residual.md#6-least-degree-six-forces-saturation-and-is-now-excluded),
least degree six forces a degree-nine top product, impossible because
nine does not divide 48. Therefore

\[
|Z|=4,\qquad |T|=9,\qquad |A|+|B|=35.             \tag{1}
\]

The [nine-top least-degree-six lemma](1485_four_central_nine_top.md#6-least-degree-six-is-sharp-regular)
makes every member of `A` sharp-regular: it has three sharp
neighbors of degree eight and three top neighbors, in each direction.
No member of `A` is a top-top product. Hence the 45 noncentral
top products all belong to `B`: there are `9²` top endpoint pairs,
of which `3²|Z|=36` have central products.

## 2. Degree-eight vertices have balanced top and sharp counts

Fix `b∈B`. Let `I,O` be its top predecessor and successor counts,
and `k⁻,k⁺` its sharp in/out counts. Its sharp neighbors are exactly
its degree-six neighbors; all other non-top neighbors have degree eight.
Ordinary degree balance and reciprocal-neighbor balance give

\[
8k^-+6(8-I-k^-)+3I
=8k^++6(8-O-k^+)+3O,
\]

so

\[
2(k^--k^+)=3(I-O).
\]

Both sharp counts lie between one and three. The only multiple of
three among the possible even differences `−4,−2,0,2,4` is zero.
Consequently

\[
I=O=t,\qquad k^-=k^+=k,\qquad t\in\{2,3,4\}.      \tag{2}
\]

Let `g(b)` count its good ordered top endpoint pairs. The
[variable-neighborhood slot bound](1485_three_central_minimum_top_output.md#a-general-top-fiber-slot-bound),
with least noncentral degree six and output degree eight, gives

\[
g(b)\le
\begin{cases}
6-2k,&t=2,\\
4-2k,&t=3\text{ or }4.
\end{cases}                                      \tag{3}
\]

The case `t=4` is impossible. Its four top predecessors have
singleton predecessor labels, and at least two have singleton
successor labels: only two tops have central profile `(1,2)`.
Its four top successors all have singleton successor labels.
Every central row contains exactly two tops of the latter kind.
Thus each of those two singleton-successor predecessor rows has
at least two noncentral pairs in the `4×4` endpoint rectangle.
All these pairs have product `b`: a lower-degree top-product
replacement could only be central or degree six, and degree six
has already been excluded as a top output. Therefore `g(b)≥4`,
contradicting (3), which gives `g(b)≤2`.

## 3. Global incidence removes the two-top case as well

Let `b₂` count members of `B` with two top neighbors. Every
other member now has three. For a top vertex `v`, let `q_v`
be its ordinary top out-degree and let `k⁻_v` be its central
in-degree. Counting all edges into the nine top vertices gives

\[
144=4\cdot3+3|A|+(3|B|-b_2)+\sum_{v\in T}q_v.
\]

Using (1), this simplifies to

\[
\sum_{v\in T}q_v=27+b_2.                         \tag{4}
\]

Every `q_v` is two, three, or four. The
[two-top-neighbor obstruction](1485_four_central_nine_top.md#4-a-small-top-neighborhood-requires-complementary-pairs)
says that a vertex with central in-degree two cannot have `q_v=2`.
Let `H₄` count tops with central in-degree two and `q_v=4`,
and let `L₂,L₄` count tops with central in-degree one and the
indicated top out-degree. Central incidence `BD=J` gives

\[
\sum_{v\in T} k^-_v q_v=36,
\qquad \sum_{v\in T} k^-_v=12.
\]

Subtracting three times the second equation from the first yields

\[
2H_4+L_4=L_2.
\]

Consequently

\[
\sum_{v\in T}q_v=27+H_4+L_4-L_2=27-H_4.
\]

Together with (4), nonnegativity forces `b₂=H₄=0`. Thus every
member of `B` has three top neighbors. Moreover every top with
central in-degree two has exactly three ordinary top successors.
The dual argument makes the ordinary top in-degree three whenever
the central out-degree is two.

## 4. There are exactly nine degree-six vertices

With `t=3`, (3) excludes sharp degree three in `B`. Sharp degree
two gives `g(b)=0`, and sharp degree one gives `g(b)≤2`.
Write `a=|A|` and let `j` count the sharp-degree-two members of
`B`. Counting sharp edges between `A` and `B` gives

\[
3a=|B|+j,\qquad j=4a-35.
\]

Thus `a≥9`, and the number of sharp-degree-one members is

\[
|B|-j=70-5a.
\]

All 45 noncentral top pairs have their products in `B`. Therefore

\[
45=\sum_{b\in B}g(b)\le2(70-5a),
\]

which gives `a≤9`. We conclude

\[
\boxed{|A|=9,\quad |B|=26,\quad j=1.}            \tag{5}
\]

This does not assert that every sharp-degree-one member of `B`
has a positive number of top representations; that is unnecessary.

## 5. The mixed central degrees force repeated central rows

For any top `v`, let `α_in,α_out` count its degree-six neighbors,
and let `q_in,q_out` count its top neighbors. Write
`k⁻,k⁺` for its central in/out degrees. Eliminate the degree-eight
neighbor counts from ordinary and reciprocal degree balance. The
result is

\[
2(\alpha_{in}-\alpha_{out})
=3(q_{in}-q_{out})-10(k^--k^+).                  \tag{6}
\]

There are two tops of central profile `(2,1)`. For either one,
§3 gives `q_out=3`, and `q_in∈{2,3,4}`. Parity in (6) forces
`q_in=3` as well, and hence

\[
\alpha_{out}-\alpha_{in}=5.
\]

Thus each of these two tops precedes at least five members of `A`.

Let `H` be the unique `(2,2)` top, and put `P_H=P`, `C_H=C`.
The two `(2,1)` tops have distinct singleton successor labels
`c₁,c₂`, precisely the two points of `Z\C`. Indeed each central
column contains exactly one top with a double predecessor set;
the columns in `C` already contain `H`.

If one of these tops `u` precedes `a∈A`, every product from
`TopPred(a)×TopSucc(a)` is central: degree six is the least
noncentral degree and cannot itself be a top output. Since
`C_u={c_i}`, all three top successors of `a` lie in `Row(c_i)`.
Both sets have size three, so

\[
TopSucc(a)=Row(c_i).
\]

The two subsets of `A` obtained this way have size at least five.
Since `|A|=9`, they intersect. Consequently

\[
Row(c_1)=Row(c_2).
\]

Equal central rows must be the two rows in `P`: each central row
contains exactly one top with double successor set, and among those
tops only `H` belongs to two central rows. Thus `P={c₁,c₂}=Z\C`.
Moreover equality of these rows forces all three double predecessor
sets to be `P`.

Apply the dual argument to the two tops of central profile `(1,2)`.
It forces all three double successor sets to be `C`.

## 6. The binary obstruction finishes the proof

All double predecessor sets are the pair `P`, and all double
successor sets are its complement `C`. This is exactly the
[disjoint rectangular incidence configuration](1485_four_central_nine_top.md#2-disjoint-pairs-give-the-binary-obstruction)
already excluded by the binary top-type theorem. The contradiction
proves the stated minimum-three, least-degree-six exclusion at
order 48.
