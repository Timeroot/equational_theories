# E1286: correlated groups and cutoff 2,767,854,535

The effective E1286 tail improves from **4,222,119,949** to
**2,767,854,535**, a reduction of 34.44%. The new numerical bound is a
constructive computer-assisted proof awaiting Lean formalization. The
underlying abstract cofiniteness theorem was already proved in Lean.

One new ingredient is fully formalized: a pointed model of order **240**,
in `Spectrum.E1083E1286.BinaryHalves.pointed240` and `model240`.
The proof uses finite fields, a linear functional and group-divisible
gluing. Its only finite case check is the four possibilities for two
elements of `ZMod 2`; it does not check a 240-by-240 multiplication table.
The constructions at orders **400** and **448**, the generalized binary
closure, and the numerical certificate are not yet formalized.

## Three half-groups: order 240

Take an affine transversal design over F32 with nine directions. Retain
six full groups, and half the points in each of the three groups whose
coordinates are x, y, x+y. Specifically, retain the kernel of any nonzero
binary linear functional chi. The three images chi(x), chi(y), chi(x+y)
have either one or three zeros, so every surviving transversal block has
size **7 or 9**. Both sizes admit idempotent E1286 models. Fill the full
groups with the existing 32-element model, and the half-groups with the
idempotent 16-element model. The total is

    6*32 + 3*16 = 240.

This is a pointed model because an idempotent point in a group stays
idempotent under gluing. The full groups need not themselves be
idempotent. Among the 1024 original transversal blocks, 768 have size 7
and 256 have size 9.

## Binary subspaces give two families of closure rules

More generally, write an even order q as a product of its maximal
prime-power factors, and use the product of the corresponding finite-field
transversal designs. In its characteristic-two field choose a binary
subspace U of dimension r, and write h = 2^(r-1). The nonzero u in U
give 2h-1 distinct directions with slopes u. In direction u retain the
points satisfying

    chi(u*z) = epsilon,     epsilon = 0 or 1.

Each selected group has q/2 points. On a transversal block z=x+u*y the
left side becomes chi(u*x+u²*y). This is a binary linear functional of u.
For epsilon=0 its zero count on U\{0} is **h-1 or 2h-1**; for epsilon=1
the count is **0 or h**. This uses only the kernel size of a nonzero
linear functional, not a search for a special design.

Suppose idempotent block models exist at b and b+h. Then:

| Selected fibre | Full groups | Total directions | Constructed order |
| --- | ---: | ---: | ---: |
| zero | b-h+1 | b+h | (2b+1)q/2 |
| nonzero | b | b+2h-1 | (2(b+h)-1)q/2 |

The first row requires b-h+1 >= 0. Each field factor of q must have at
least one fewer elements than the number of directions, and the
characteristic-two factor must have at least 2h elements. These conditions
let us choose all the required distinct directions in every field factor;
the binary retention condition depends only on the even factor. Models of
orders q and q/2 fill the groups. If both are idempotent the result is
idempotent as well.

There is also the common-point version: use pointed fillings of orders
q+1 and q/2+1, identify their distinguished points, and add 1 to the
constructed order. Pairs away from that point lie either in one group or
on exactly one transversal block, so the usual gluing proof applies.

Order 400 uses b=9, h=4, q=32 and the nonzero fibre: nine full groups and
seven half-groups, with blocks of sizes 9 and 13. There are 128 blocks of
size 9 and 896 of size 13. All its 160,000 instances of E1286 are also
checked independently by the reconstruction script.

## An idempotent seed at order 448

The analogous construction over F49 uses one representative u for each
of the eight projective points of the two-dimensional F7-space F49.
Their slopes u^6 are distinct: two nonzero elements have equal sixth
powers precisely when their ratio lies in F7*. Retain the seven points
with chi(u*z)=0 in each of these eight groups, where chi is a nonzero
F7-linear functional. Add eight full groups of size 49.

On a transversal block the relevant values are chi(u*x+u^7*y), an
F7-linear functional on F49. Its projective kernel has either **one or
eight** points. Thus the surviving blocks have sizes **9 or 16**, with
2352 of the former and 49 of the latter. Fill the groups with idempotent
models at 49=7² and 7. The result has order

    8*49 + 8*7 = 448

and is idempotent. It satisfies both E1083 and E1286. The reconstruction
script independently checks both identities on all 200,704 pairs, and
checks idempotence. No large table is stored in the repository.

## Numerical certificate and induction

`scripts/spectrum_effective_bound.cpp` has an optional binary-simplex
closure mode. It combines the previous ring seeds, the new idempotent
448 seed, Cartesian products, common-point gluing, ordinary truncated
transversal designs, and the binary rules above, through order 10^9.
Its idempotent bitmap supplies new block pairs, including 4032/4033.
The old interval certificate above 4,486,445,592 is retained; its source
models remain available in the expanded closure.

The new compressed prefix covers
**2,767,854,535 through 4,486,445,592**. It has 156,242 translated-prefix
records and two isolated constructions:

* 2,790,586,698 = 71 * 39,304,038, with both factors in the source bitmap.
* 2,777,823,960 = 15 * 185,188,264, from the zero-fibre binary rule
  b=7, h=2, q=370,376,528. The maximal field factors are 16 and
  23,148,533; the q and q/2 group fillings are in the source bitmap.

The independently replayed finite interval extends through 5*10^12.
The unchanged 22,000-integer sieve gives a suitable TD(1009,q) in every
window of that length. With C=2,767,854,535, put

    T = C + 1008*22000 = 2,790,030,535,
    N = 1009*T = 2,815,140,809,815.

The certified interval reaches beyond N. The existing strong-induction
argument writes every n>N as 1008q+r with C<=r<T<=q<n, and fills the two
group sizes using the finite certificate and induction. The block models
at 1008 and 1009 finish the construction. Order C-1 remains unfilled by
this computation; no nonexistence claim is made.

To reconstruct the small models and replay the numerical proof:

```sh
python3 scripts/spectrum_binary_half_design.py
python3 scripts/spectrum_effective_tails.py --law 1286 --jobs 4
```

The second command regenerates the source bitmaps and checks their hashes,
all ring identities, the 448 seed, the complete interval cover, the two
isolated constructions and the sieve. `--reuse-bitmaps` skips regeneration
but still checks the recorded hashes. The independent cover checker does
not trust the search optimizer. The ordinary C++/Python computations and
the binary closure theorem remain outside Lean's kernel.
