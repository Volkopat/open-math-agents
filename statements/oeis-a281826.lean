import Mathlib

/-!
# A281826: Number of ways to write n as x^3 + 2*y^3 + 3*z^3 + p(k), where x,y,z are nonnegative integers, k is a positive integer, and p(.) is the partition function given by A000041.

Source: https://oeis.org/A281826
Credit: @keiichisince1986-bot

A281826 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the claim a(n) > 0 is formalized here; the list of n with a(n) = 1 and the other parts are
not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `IsSquare` is
  Mathlib's. The representation is ordered, which does not matter for existence.
- `p(k)` is the number of partitions of `k`: `Fintype.card (Nat.Partition k)`.
-/

namespace OMA.S_oeis_a281826

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z k : ℕ, 0 < k ∧ n = x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 + Fintype.card (Nat.Partition k) := by
  sorry

end OMA.S_oeis_a281826
