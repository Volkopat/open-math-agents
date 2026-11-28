import Mathlib

/-!
# A086552: Numbers x such that tau(x)/tau(x-1) is an integer, where tau() is the number of divisors function.

Source: https://oeis.org/A086552
Credit: @divmxnd0x

Conjecture (1) (stated in A086552): `tau(x)/tau(x-1) = n` has solutions for every `n`.

Formalization notes:
* `tau(x)/tau(x-1) = n` is written `tau(x) = n * tau(x-1)`, with `x ≥ 2` (the terms of A086552
  start at `2`; `tau(0)` is not defined in the OEIS). Here `n` ranges over the positive integers.
* Only part (1) of the comment is formalized. (Part (2), "if `x` is the smallest number with
  `tau(x)/tau(x-1) = n > 1` then `x - 1` is prime", fails literally at `n = 2`, where the smallest
  solution is `x = 2` and `x - 1 = 1`; it is not stated here.)
-/

namespace OMA.S_oeis_a086552

/-- Part (1): for every `n ≥ 1` there is `x ≥ 2` with `tau(x) = n * tau(x-1)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ x : ℕ, 2 ≤ x ∧
    x.divisors.card = n * (x - 1).divisors.card := by
  sorry

end OMA.S_oeis_a086552
