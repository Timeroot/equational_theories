# Six central vertices: complementary triple blocks are impossible at first degree seven

Research note, 20 September 2026. This is an analytic finite E1485
result, not a Lean theorem or a finite enumeration. Assume minimum
translation degree four, six central vertices, and least noncentral
top-product degree seven.

**Subsequent completion:** the [entire six-central degree-seven case](1485_min_four_six_central_seven_exclusion.md)
is now excluded. The argument below remains a valid independent local
obstruction, but its longer case split is not needed in the final proof.

**Theorem.** No top vertex has disjoint central predecessor and
successor blocks both of size three.

The proof uses the [maximal-block first-output gap](1485_maximal_central_block_first_output_gap.md)
and the [one-sided witness and first-output results](1485_min_four_six_central_seven_profiles.md).
It does not follow merely from the central incidence equations.

## 1. A complementary triple tile leaves only singleton-sided tiles

Suppose a top `v` has predecessor block `A` and successor block
`B`, where `A,B` are complementary triples of central labels.
Uniqueness of a central middle gives, for every top `x`,

\[
|P_x\cap B|\le1,\qquad |C_x\cap A|\le1.                  \tag{1}
\]

The central rectangles `P_x×C_x` partition the full central
square. Thus for `x≠v`, its predecessor block cannot meet `A`
and its successor block meet `B` simultaneously: such a cell
would already belong to `A×B`.

Consequently every other tile whose predecessor block has size
greater than one has singleton successor block in `A`. Indeed,
(1) forces its predecessor block to meet `A`; its successor
block is then contained in `A` and has size at most one by (1).
Dually every other tile with successor block of size greater
than one has singleton predecessor block in `B`.

The maximal-block theorem excludes `(3,1)` and `(1,3)`
profiles at first degree seven. Therefore `v` is the only top
with a size-three block in either direction. Every other tile has
both block sizes at most two and at least one singleton side.

The one-sided witness theorem, followed by duality if necessary,
supplies a top `u` with `|P_u|=2`, `|C_u|=1`. A degree-seven
first output in this row has top profiles `U,V` of common size
four or five. The blocks `P_x` for `x∈U` partition the six
central labels, as do the blocks `C_y` for `y∈V`. Their
intersection matrix

\[
K_{xy}=|C_x\cap P_y|
\]

is zero-one and three-regular.

## 2. Four top neighbors would require two triple columns

Suppose `|U|=|V|=4`. The predecessor-block partition of `U`
contains the pair `P_u`, so its shape is `2+2+1+1`. By
Section 1, both pair-block vertices have singleton successor blocks.
The matrix `K` is a four-by-four crown.

Let the two singleton row labels be `a_1,a_2`. They are
distinct because crown rows are distinct. The two columns common
to their supports both contain `a_1,a_2` in their predecessor
blocks. Each of the other two rows misses one of these columns
and hits the other. To hit the latter while missing the former,
it needs a label outside `{a_1,a_2}`. Thus both common columns
have predecessor blocks of size at least three. This contradicts
the fact that `v` is the unique top with such a block.

## 3. Five top neighbors give incompatible repeated columns

Now suppose `|U|=|V|=5`. The predecessor partition of `U`
has the pair `P_u` and four singletons. The successor partition
of `V` likewise has one pair and four singletons. Neither
profile contains `v`, whose relevant block would have size three.

The unique successor-pair tile in `V` has singleton predecessor
block in `B`. Its column requires three rows whose successor
blocks meet `B`. If `P_u` were a mixed `A/B` pair, the
four predecessor singletons of `U` would consist of two in `A`
and two in `B`. The vertex `u` and both `A`-singleton vertices
have singleton successor blocks in `A`, leaving at most two
rows to meet that column. This is impossible. Hence `P_u⊂A`.

There are now exactly two vertices of `U` whose predecessor
blocks cover `A`: `u` with its pair, and the remaining
`A`-singleton. Their successor blocks are singleton labels
`a_1,a_2∈A`. These labels are distinct. Otherwise the central
column `Col(a_1)` would contain both tops covering `A`; its
remaining two predecessor blocks would have to cover all three
labels of `B`, contrary to (1).

The other three members of `U` have singleton predecessor blocks
in `B`. Every column whose predecessor block is a singleton in
`B` must meet all three of these rows, since neither of the two
singleton-`A` rows can meet it and its column sum is three.

The successor pair of `V` is either mixed `A/B` or lies in
`B`: it cannot contain two `A` labels by (1).

* For a mixed pair, two of the remaining successor singletons
  lie in `B`. These two tiles, and the pair tile itself, all
  have singleton predecessor blocks in `B`. The two singleton-
  `A` rows are zero on these three columns, leaving only two
  columns in which to obtain their required row sum three.
* For a pair inside `B`, one remaining successor singleton is
  in `B`, and the other three are in `A`. There are two
  singleton-`B` predecessor columns, and both singleton-`A`
  rows must be one on each of the other three columns. Their
  predecessor blocks therefore contain both distinct labels
  `a_1,a_2`. All have size at most two, so those three blocks
  are identically `{a_1,a_2}`. Each of the other three rows
  already meets both singleton-`B` columns and must meet exactly
  one of these three identical columns. That is impossible.

Both possible top-profile sizes have been excluded, proving the
theorem. The independent
[singleton-label separation theorem](1485_singleton_central_labels_first_output.md#4-at-minimum-four-and-central-count-six-the-triple-blocks-are-fixed)
forces any `(3,3)` tile in this branch to have complementary
blocks. Combining the two results therefore excludes all `(3,3)`
tiles, not merely the disjoint ones. The separate `(3,2)` and
`(2,3)` possibilities are handled by the stronger containment
and two-singleton-label arguments in the
[complete six-central degree-seven exclusion](1485_min_four_six_central_seven_exclusion.md).
That full exclusion has a shorter proof chain and does not need
this complementary-triple argument.
