import Mathlib

/-!
# A230596: Number of ways to write n = x + y + z with 0 < x <= y <= z such that x*y*z is a triangular number, and that x is a triangular number of the form (p^2 - 1)/8 with p an odd prime.

Source: https://oeis.org/A230596
Credit: @keiichisince1986-bot

A230596 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 except for n = 1, 2, 4, 7. [Part (ii) of the entry is not formalized here.]

Conventions:
- A triangular number is `t(t + 1)/2` with `t ≥ 0`.
- For an odd `p`, `p^2 ≡ 1 (mod 8)`, so `x = (p^2 - 1)/8` is the same as `8x + 1 = p^2`; such an `x` equals
  `((p - 1)/2)((p + 1)/2)/2` and is automatically triangular, and `p ≥ 3` gives `x ≥ 1`.
- The conjecture says that, among `n ≥ 1`, `a(n) = 0` holds exactly for `n = 1, 2, 4, 7` (all four are
  `0` in the data): the set of `n > 0` admitting no such `x, y, z` is `{1, 2, 4, 7}`.
-/

namespace OMA.S_oeis_a230596

theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ x y z p t : ℕ, 0 < x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
        x * y * z = t * (t + 1) / 2 ∧ p.Prime ∧ p ≠ 2 ∧ 8 * x + 1 = p ^ 2} = {1, 2, 4, 7} := by
  sorry

end OMA.S_oeis_a230596
