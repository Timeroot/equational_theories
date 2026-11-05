# E115: a finite-image obstruction via Boolean simulation

**Formalized in Lean, 3 November 2026.** The finite image obstruction is
`Parastrophes.Eq115BooleanTurn.no_singleEquation`, registered as
`Parastrophes.Catalogue.right_noSingleEquation115_fin` in
[`Equation115FiniteImageObstruction.lean`](../equational_theories/Parastrophes/Equation115FiniteImageObstruction.lean).
The stronger theorem `boolean_theory` proves the transfer of every identity.
All dependencies use only `propext`, `Classical.choice`, and `Quot.sound`;
there are no `sorry` or `native_decide` certificates.

## Exact conditional characterization

Write D for right division, and c(x)=D(x,D(x,x)). E115's right-division image
is exactly the right quasigroups satisfying E221,

    x = D(D(y,D(x,y)),x).

This works on arbitrary carriers. Column cancellation gives
D(y,D(x,y))=c(x). Rotating gives D(D(x,y),c(x))=c(y), from which c is an
injective endomorphism, hence a finite automorphism. If M is the recovered
multiplication, c(x)=M(x,x), and c(M(x,y))=D(y,x).
These statements are proved in `Equation115RightImage.lean`.

The Boolean magma B(x,y)=(NOT x) AND y satisfies E221 but is not a right
quasigroup. The new construction shows something stronger: **every identity
valid in all finite E115 right images holds in B**. Consequently no single
identity, or even any collection of ordinary identities, characterizes those
images among finite magmas.

## A finite partial turn

Work over the free abelian group W with height coordinate and two infinite
families of extra coordinates, called productive and reserved. Put s=(1,0,0).
Write h for height and r for projection onto the reserved coordinates. We
construct a partial permutation t in disjoint three-cycles with cycle sum -s.
Start with (0,-2s,s). Maintain these conditions on every defined pair x→t(x):

* h(x)>0 implies h(t(x))=0 and r(t(x))=0.
* h(x)<0 implies 0≤h(t(x))<-h(x).
* h(x)=0 implies h(t(x))≤0; if also r(x)=0, the inequality is strict.

To define t at a new point a, choose a fresh coordinate, absent from a and
all existing points, and its unit vector e. Use a productive coordinate if
h(a)>0 or h(a)<-1, and a reserved coordinate otherwise. Put q=-s-a-e.
If h(a)>0, add the cycle (a,e,q). Otherwise add (a,q,e).
The fresh coordinate has coefficients 0,+1,-1 on its three points, so the
cycle is new and has three distinct points. Its sum is -s. Checking the four
height cases h(a)>0, h(a)<-1, h(a)=-1, and h(a)=0 verifies the invariants.
In the last two cases the potentially troublesome zero→zero edge starts at a
point with a nonzero fresh reserved coordinate. It therefore does not violate
the strict inequality for zero-height points with r=0.

## Simulating Boolean term evaluations

Let P consist of points of nonnegative height whose reserved coordinates
vanish whenever the height is zero. Define the partial product

    D(x,y)=y-t(x-y).

Extend t whenever a term evaluation needs an undefined difference. Then P is
closed under each product so constructed, and the map

    beta(x) = true if h(x)=0, false if h(x)>0

satisfies beta(D(x,y))=(NOT beta(x)) AND beta(y).
Indeed, when h(x)>h(y), t(x-y) has height zero and no reserved coordinates,
so the output has height h(y). When h(x)<h(y), the strict negative-input
bound makes the output positive. When the heights are equal and positive,
the output is positive. When both are zero, their difference has no reserved
coordinates, so the strict zero-input bound again makes the output positive.
Only the first case produces a zero-height output, and then its reserved
coordinates vanish.

For an identity failing in B, assign 0 to each true variable and s to each
false variable, and evaluate both sides using this construction. It uses
finitely many turns. Their outputs have distinct Boolean values, hence
one has zero height and the other positive height. In particular they differ.

## Completing the finite fragment in an actual finite image

Scale the height coordinate by 3, leaving the other coordinates unchanged;
write j for this embedding and v for the height unit vector. For each partial
cycle (a,b,c), use the reversed shifted triple

    (j(a)+v, j(c)+v, j(b)+v).

Its sum is zero. All its points have height congruent to 1 modulo 3, so are
nonzero over the integers. They are pairwise distinct across all triples.
Restrict to the finitely many coordinates used, and reduce modulo an integer
N large enough to preserve those distinctions, their nonzeroness, and the
distinct final outputs. This gives triples in V=(Z/NZ)^d.

The already proved `FiniteTriangleTrades.exists_turn` rearranges their nine-
point orbit blocks on V×V. It gives Q with Q³=id, z+Qz+Q²z=0, and the
prescribed reversed cycles on the first coordinate axis. Set

    A(z)=Q(z+(v,0))-(v,0).

Then A³=id, A(0)=(3v,0), and z+A(z)+A²(z)=-(3v,0). The formulas

    M(x,y)=y+A(y-x),       D(x,y)=y-A²(x-y)

therefore give an E115 magma and its exact right division, by
`Equation115SquareTranslations.source_law` and `isRightDivision`.
On all the queried differences, A² reproduces the original partial t.
Both finite term evaluations consequently reproduce the chosen fragment,
and remain distinct. This refutes the proposed identity in a finite image.

If a single identity characterized finite images, it would hold in all of
them, hence in B by the preceding construction. The characterization would
then make B an image, contradicting its nonbijective columns. This is the
claimed negative answer. In Lean, `Equation115BooleanTurn.lean` builds a
completed turn using a greedy chain; `FiniteAbelianSeparation.lean` preserves
finitely many integer points in finite cyclic quotients; and
`Equation115FiniteImageObstruction.lean` transfers each finite term computation
using `FiniteTriangleTrades.exists_turn_on_points`. No uniform bound on
the size of these finite models is required.

## A further consequence: no uniform reverse recovery term

This additional consequence is a paper corollary, not a separately registered
Lean theorem. The same construction with every input zero keeps every unary term's height
nonnegative. Since c_D(x)=x+(3v,0), choosing N large also ensures c_D(T(0))≠0.
Thus no fixed unary D-term uniformly inverts c in all finite images. Nor can a
fixed binary D-term recover M: such a term B would make B(x,c(x)) a uniform
inverse of c, since c(M(x,c(x)))=D(c(x),x)=x.
This is about **reverse** recovery, not the catalogue's source-to-division
uniform-term field. It must not be counted as closing that field.


## The same witnesses close E873's finite left image

The opposite operation N(x,y)=x+A(x-y) satisfies E873 as well. Its square
is x+s, and the triangle identity gives

    y-(x+s+A(x-y)) = A²(x-y).

Consequently N(y,N(N(x,x),N(y,y)))=y+A³(x-y)=x. This uses A³=id,
which was already available in the finite construction. The exact lemma is
`Eq115SquareTranslations.opposite_source_law873`. This is a property of the
constructed family, not a general implication from E115 to E873.

The left division of N is the opposite of the right division used above.
The same finite computations therefore simulate Boolean x AND NOT y. It
has a constant false row, so is not a left quasigroup, yet satisfies every
identity valid in all finite E873 left images. Thus no collection of ordinary
identities characterizes those images either. The result is formalized and
registered as `Parastrophes.Catalogue.left_noSingleEquation873_fin` in
[`Equation873FiniteImageObstruction.lean`](../equational_theories/Parastrophes/Equation873FiniteImageObstruction.lean).
The original finite-transfer proof is shared through `finite_fragment_common`
and `boolean_theory_from_fragments`; no new finite tables are needed.
