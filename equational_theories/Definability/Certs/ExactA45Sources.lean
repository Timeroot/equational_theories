import equational_theories.Definability.ExactAut5A45

/-!
# Structural certificate sources: `Magma.exactA45`

For each of the following magmas, drawn from the `16` magmas on `Fin 5` whose automorphism group is
exactly the order-`12` group of `Magma.permEA45`, the equations it satisfies that no earlier listed
magma does. Together they are the `85` equations that are worth using as the *source* `L'` of a
`Magma.exactA45` certificate -- the rest have such a model too, but the resulting facts are already
implied by what is on the board. `3` members cover them.

This file is generated; see the module docstring of `Definability.ExactAut5`.
-/

set_option maxHeartbeats 1000000
-- each `rfl` below reads one entry out of `Magma.memArrA45`, and reading entry `k` recurses `k`
-- deep into the list behind the array
set_option maxRecDepth 100000

/-- `58` equations satisfied by `Magma.exactA45 0`, and by no earlier member of the cover. -/
theorem exactA45_satisfies_0 :
    Satisfies (Magma.exactA45 0) [
      40, 316, 320, 368, 369, 3276, 3282, 3286, 3293, 3294, 3298, 3303, 3473, 3485, 3486, 3497,
      3500, 3501, 3502, 3682, 3686, 3688, 3689, 3691, 3692, 3693, 3699, 3700, 3704, 3709, 3879,
      3891, 3892, 3903, 3906, 3907, 3908, 4092, 4094, 4095, 4097, 4098, 4099, 4106, 4276, 4280,
      4346, 4355, 4389, 4390, 4484, 4497, 4499, 4500, 4591, 4592, 4609, 4623
    ] := by decide!

/-- `26` equations satisfied by `Magma.exactA45 12`, and by no earlier member of the cover. -/
theorem exactA45_satisfies_1 :
    Satisfies (Magma.exactA45 12) [
      481, 695, 887, 978, 1101, 1384, 1496, 1523, 1537, 1710, 1740, 1902, 1993, 2105, 2132, 2146,
      2319, 2602, 2725, 2755, 3008, 3161, 4325, 4461, 4491, 4620
    ] := by decide!

/-- `1` equations satisfied by `Magma.exactA45 4`, and by no earlier member of the cover. -/
theorem exactA45_satisfies_2 :
    Satisfies (Magma.exactA45 4) [
      851
    ] := by decide!
