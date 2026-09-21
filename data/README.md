## Definability data

The `definability_*.json` files include witness tables, counting certificates,
and inputs to the `scripts/definability_*_check.py` checkers and Lean generators.
Some checkers discover whole families by filename glob, so an individual file
need not be named explicitly in the source to be required. Keep these inputs
and the data linked from mathematical documentation; unreferenced search-pass
summaries are disposable. JSON itself is not a proof oracle: generated Lean
declarations and their axiom checks establish the formal results.

The optional `definability_1483_lrat/` bundle is deliberately excluded from Git
(734 MiB). Its small [manifest](definability_1483_order_eleven.json) is retained;
the [E1483 proof guide](../docs/definability_1483_order_eleven.md) explains the
registered Lean `sorry` and how to restore the computational proof locally.

## Spectrum data

See [spectrum/README.md](spectrum/README.md): `witnesses.json` is input containing
candidate finite tables; `bv_cases.json` supplies SAT-core selections rechecked
by Lean; `catalogue.json` is a generated index of Lean statements
and their checked proof statuses. Proof obligations and provenance live beside
their Lean declarations, not in a separate data file.

Historical E1485 finite-case certificates under `1485_certificates/` are also
local-only. Some exploratory scripts can replay them, but the full square /
twice-square spectrum proof needs no certificates or finite enumeration.

## Vampire data

The vampire json describes results of vampire. It comprises two dictionaries:
methods and values. The methods are from method_id to solver configurations.
Values map a pair of equation ids x, y to a triple describing value, time,
method_id. The pair is concerned with the implication x=>y. The value comes
from the enum below. I.e. 0 means that the implication was refuted, 1 means
that the implication was proven.

````
class Res(Enum):
    """Possible result for single implication."""

    IMPL_FALSE = 0
    IMPL_TRUE = 1
    IMPL_UNKNOWN = 2
````

## Higman-Neumann data

The JSON file `Higman-Neumann.json` lists 213 equation ids, the
corresponding law, the id of a "parent law" which specializes to this
law, and the class: 179 "HN-equivalent" equations whose models are
groups equipped with division, 21 "finite-equivalent" equations whose
finite models have the same property, and 13 "unknown-candidate"
equations for which it is unknown whether they have finite or infinite
non-group models.
