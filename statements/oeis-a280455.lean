import Mathlib

/-!
# A280455: Number of ways to write n as x*(3x-1)/2 + y*(3y+1)/2 + p(z), where x,y,z are nonnegative integers with z > 0, and p(.) is the partition function given by A000041.

Source: https://oeis.org/A280455
Credit: @keiichisince1986-bot

A280455 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Further parts are not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise. The count is of
  ordered representations, which does not matter for existence.
- `x(3x-1)/2` and `y(3y+1)/2` are exact natural-number divisions; `p(z)` is `Fintype.card (Nat.Partition z)`.
-/

namespace OMA.S_oeis_a280455

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z : ℕ, 0 < z ∧
      n = x * (3 * x - 1) / 2 + y * (3 * y + 1) / 2 + Fintype.card (Nat.Partition z) := by
  sorry

end OMA.S_oeis_a280455
