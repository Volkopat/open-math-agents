import Mathlib

/-!
# A215462: Number of decompositions of 2n into ordered sums of two odd nonprimes.

Source: https://oeis.org/A215462
Credit: @keiichisince1986-bot

A215462 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) is never zero for n > 19, verified to 10^9.

Conventions:
- Odd nonprimes include `1` (as in the identity A002372(n) + A215461(n) + a(n) = n). The offset is `0`.
- `a(n) > 0` means that `2n = a + b` with `a` and `b` odd nonprimes.
-/

namespace OMA.S_oeis_a215462

theorem main :
    ∀ n : ℕ, 19 < n → ∃ a b : ℕ, Odd a ∧ Odd b ∧ ¬ a.Prime ∧ ¬ b.Prime ∧ a + b = 2 * n := by
  sorry

end OMA.S_oeis_a215462
