import Mathlib

/-!
# A215461: Number of decompositions of 2n into ordered sums of one prime and one nonprime.

Source: https://oeis.org/A215461
Credit: @keiichisince1986-bot

A215461 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) is never zero for n > 5, verified to 10^9.

Conventions:
- As the identity A002372(n) + a(n) + A215462(n) = n and the examples of the entry show, the summands are odd
  (for example `30 = 29 + 1`, so `1` counts as a nonprime). The offset is `0`.
- `a(n) > 0` means that `2n = p + q` with `p` an odd prime and `q` an odd nonprime.
-/

namespace OMA.S_oeis_a215461

theorem main :
    ∀ n : ℕ, 5 < n → ∃ p q : ℕ, Odd p ∧ Odd q ∧ p.Prime ∧ ¬ q.Prime ∧ p + q = 2 * n := by
  sorry

end OMA.S_oeis_a215461
