# Order 24 is absent from the E1485 spectrum

Research note, 18 September 2026. **There is no E1485 magma of order 24.**
The original proof used pen-and-paper finite structure arguments and two
small explicit incidence enumerations. The general
[five-central exclusion](1485_five_central_binary_blocks.md) now replaces
one enumeration, leaving only the four-central finite check in this
proof chain. It is not yet a Lean theorem, and its
finite calculations should not be confused with a fully analytic proof.
It does not prove the general square-or-double-square conjecture.

## Proof by minimum translation degree

Write `d(x)=|Row(x)|=|Col(x)|`, and let `r=min d`, `s=max d`.
The [finite structure theorems](1485_graph_research.md) give `rs=24`
and say that every degree divides 24. Thus `r∈{1,2,3,4}`.

* If `r=1`, the constant-row classification forces the order to be
  a power of two, excluding 24.
* If `r=2`, the [four-central-vertex theorem](1485_two_central_exclusion.md)
  gives a full central core. The
  [six-times-square exclusion](1485_six_times_square_full_core.md)
  excludes `24=6r²`.
* If `r=4`, then `s=6`. The only divisors of 24 between four and
  six are four and six, so there are precisely two degrees. The
  [two-degree theorem](1485_two_degree_lower_bound.md) forces `s=2r`,
  a contradiction.
* It remains to exclude `r=3`, as follows.

## The minimum-degree-three case

The degree classes are exactly `3,4,6,8`; write `m` for the number
of central vertices, those of degree three. The
[large-central reduction](1485_order_twenty_four_large_central.md)
gives `3≤m≤6`. All four possibilities are now excluded:

| Central count | Argument | Proof status |
| --- | --- | --- |
| 3 | [Profile reduction](1485_order_twenty_four_three_central_reduction.md), then the [nine/three](1485_order_twenty_four_three_central.md) and [six/six](1485_order_twenty_four_six_six_profiles.md) arguments | Pen-and-paper |
| 4 | [Incidence reduction](1485_order_twenty_four_small_central.md), then [at most four admissible profiles](1485_order_twenty_four_four_central_finite.md), whereas at least six are required | Pen-and-paper plus 285-diagram finite check |
| 5 | [General five-central exclusion](1485_five_central_binary_blocks.md), independent of total order | Pen-and-paper |
| 6 | [Two-profile reduction and pair-count contradiction](1485_order_twenty_four_six_central.md) | Pen-and-paper |

This exhausts the possible minimum degrees and proves the exclusion.

## Reproducing the finite steps

```sh
python3 scripts/1485_m4h9_incidence_check.py --all
python3 scripts/1485_m5h9_incidence_check.py
```

The first, still used above, checks 285 normalized central diagrams, presented as 88
classes under central relabeling and duality; runtime is approximately
0.4 seconds. The second uses the 34 graphs on five central points to
generate 8,887 exact covers; runtime is approximately 23 seconds.
The second is now historical, superseded by the analytic five-central
proof. Both use only the Python standard library and exact finite arithmetic.
Their notes explain exhaustiveness and the reduction from magmas.
Neither step relies on SAT results or certificates.

All statements on this page are currently research-note results.
Kernel-checked versions of the general structural lemmas and finite
enumerations are further work; no new Lean axioms or `sorry` declarations
were added for this exclusion.
