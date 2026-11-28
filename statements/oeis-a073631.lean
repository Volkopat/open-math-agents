import Mathlib

/-!
# OEIS A073631: Nonprimes k such that k divides 3^(k-1) - 2^(k-1)

Source: https://oeis.org/A073631
Credit: @unserus

OEIS (Alexander Adamchuk, May 04 2007): "It appears that a(1) = 1 and
a(4) = 529 = 23^2 are the only perfect squares in a(n). [...] Conjecture: All
nonsquarefree terms of a(n) are the multiples of 23^2."

The terms are the positive nonprime `k` with `k ∣ 3^(k-1) - 2^(k-1)` (the
offset starts at a(1) = 1, so `k = 0` is excluded). The subtraction is in `ℕ`,
which is harmless because `2^(k-1) ≤ 3^(k-1)`. Both observations are stated,
as a conjunction: the only perfect squares among the terms are 1 and 529, and
every term that is not squarefree is divisible by `23^2 = 529`.
-/

namespace OMA.S_oeis_a073631

/-- The terms of A073631. -/
def a073631Set : Set ℕ :=
  {k | 0 < k ∧ ¬ k.Prime ∧ k ∣ 3 ^ (k - 1) - 2 ^ (k - 1)}

/-- The only squares in A073631 are 1 and 529, and every nonsquarefree term is a
multiple of 23^2. -/
theorem main :
    (∀ k ∈ a073631Set, IsSquare k → k = 1 ∨ k = 529) ∧
    (∀ k ∈ a073631Set, ¬ Squarefree k → 23 ^ 2 ∣ k) := by
  sorry

end OMA.S_oeis_a073631
