# Fifteen tops and ten degree-five elements cannot have eight three-profiles

Research theorem, 20 September 2026. This is an independently audited
analytic finite E1485 proof, not a Lean theorem. No computation or SAT
premise is used.

**Theorem.** At order forty and minimum degree four, eight central
elements, fifteen tops, and ten degree-five elements cannot coexist
with exactly eight degree-five three-profiles.

Suppose otherwise. There are eight elements in `A_3` and two in
`A_4`, according to whether the common top-profile size is three or
four. For a top, use `P,C,α,β` as in the
[profile-bound note](1485_order_forty_eight_central_ten_five_profile_bound.md).

The three predecessor blocks of any `A_3` element partition eight
central labels as `3,3,2`. Thus a top with `P=1` can have successors
only in the two-element class `A_4`, giving `α≤2`. But `C=1`
forces `α≥3`, so there are no type-`(1,1)` tops.

Let `D_u` be the nonnegative integer slack in the profile-bound
inequality:

\[
 D_u=-3PC+8(P+C)-19
       -(P-2)\alpha-(C-2)\beta-\mathbf1_{P=C=2}.
\]

The exact total slack is

\[
                \sum D_u=320-19\cdot15-4\cdot8-n_{22}
                         =3-n_{22}\le3.                 \tag{1}
\]

We show that every type-`(1,3)` top has strictly positive slack.
At such a top, `D_u=4+α−β`. Equality would force `α=0,β=4`.
Reciprocal balance then says `O−I=−2`. Since `O≥3` and
`I+P+β≤10`, this forces `I=5,O=3`, leaving no ordinary
degree-eight predecessor.

Count the fifteen top inputs in its multiplication column. Central
outputs account for four. If `γ` of its four degree-five predecessors
belong to `A_3`, those outputs account for `3β−γ=12−γ`.
There are no degree-eight outputs, and no top outputs either, by
[small-block confinement](1485_top_return_small_blocks.md): this top's
`C` block has size three, so it cannot be the second input of a
top-valued top product. Consequently

\[
                              15=4+12-\gamma,
\]

so `γ=1`. This would leave three distinct predecessors in `A_4`,
although `|A_4|=2`. Hence equality is impossible and `D_u≥1`.
The dual argument gives the same lower bound at every type-`(3,1)`
top.

Finally, the central mixed moment, with `n11=0`, is

\[
 n_{13}+n_{31}=n_{33}+4\ge4.
\]

Thus `ΣD_u≥4`, contradicting (1). This excludes the proposed
eight-three-profile branch. Lower values of the three-profile count
are not excluded by this argument.
