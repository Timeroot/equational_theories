# A symbolic follow-up for the six-element E117/E1453 witnesses

Status: a complete pen-and-paper obstruction, checked against the enumerated
binary clone, **awaiting Lean formalization**. Do not add these as certified
arrows yet. The tables are models 18 and 15 in
`data/definability_six_element_clones.json`. The prospective conclusions are
E117 ↛ E411 and E1453 ↛ E411 for finite term-structural definability.

## The source models

On integers modulo six define `x*y = y+(-1)^x`. This satisfies
E117, `x = y*((x*y)*x)`: the parity of `x*y` is opposite that of `y`, so the
inner product is `x-(-1)^y`, and multiplication on the left by `y` returns `x`.
The opposite operation `x∘y = x+(-1)^y` satisfies E1453,
`x = (x∘y)∘(y∘(x∘z))`, by the same cancellation of signs.
Both operations depend on both arguments and flip parity on the diagonal.

Write a point as `(p,c)` with `p` a bit and `c` in the field with three elements,
corresponding to `2c+p` modulo six. The first operation is

```
(p,c) * (r,d) = (1-r, d+r-p).
```

## A family containing all binary terms

Choose one argument `v` (either `x` or `y`), a bit `e`, and two field parameters
`a,b`. Define

```
F(v,e,a,b)(x,y) = (p_v XOR e, c_v + a*p_x + b*p_y + a+b).
```

There are 36 operations, and the two projections occur with `e=a=b=0`.
The source `*` is `F(y,1,-1,1)`; its opposite is `F(x,1,1,-1)`.
This family is closed under composition along either source operation.

For closure under `*`, let the two inner operations be `F_i,F_j`. The result
chooses `v_j`, flips its parity bit, and adds `p(F_j)-p(F_i)` to its field
coordinate. Write `s_i=1-2e_i` and `s_j=1-2e_j`. Then

```
a' = a_j + s_j*[v_j=x] - s_i*[v_i=x],
b' = b_j + s_j*[v_j=y] - s_i*[v_i=y].
```

The constant coordinate term is `a_j+b_j+e_j-e_i`, which equals `a'+b'`
because `s_j-s_i = -2(e_j-e_i) = e_j-e_i` in characteristic three. Thus the
result is again a family member. Composition along the opposite source swaps
the two inner operations in this formula, so it is closed as well. Induction
on terms gives the required upper bound on both binary clones.

## E411 forces a property incompatible with recovery

E411 says `x = x*(x*(x*(x*x)))`, or `L_x^4(x)=x`.

If `e=0`, each parity fibre is closed under the operation. Every term of this
companion still preserves the parity of a diagonal input, so it cannot recover
either source, whose diagonal flips parity.

Suppose `e=1`. If `v=x`, every output of the left row `L_x` has parity opposite
to `x`. In particular `L_x^4(x)≠x`, contradicting E411.

If `v=y`, apply a fixed left row four times. Its parity returns to the starting
value. The coordinate increment is `a*(p_x+1)` (four is one modulo three; the
terms involving `b` cancel). Taking an even `x` in E411 forces `a=0`. The
operation now depends only on `y`. Every term of it ignores one argument, so it
cannot recover either source, which depends on both arguments.

Thus every E411 companion in the source term clone either preserves parity
fibres or is unary. Neither permits recovery. This replaces a 36-operation
multiplication-table certificate with a composition formula and two short
invariant arguments.
