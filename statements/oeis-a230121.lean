import Mathlib

/-!
# A230121: Number of ways to write n = x + y + z (0 < x <= y <= z) such that x*(x+1)/2 + y*(y+1)/2 + z*(z+1)/2 is a triangular number.

Source: https://oeis.org/A230121
Credit: @keiichisince1986-bot

A230121 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 except for n = 1, 2, 4, 5, 7, 12. [The entry continues with a stronger form
(x, y, z distinct for n >= 20) and parts (ii) and (iii); only the first claim of part (i) is
formalized here.]

Conventions:
- A triangular number is `t(t + 1)/2` with `t ≥ 0`.
- The conjecture says that, among `n ≥ 1`, `a(n) = 0` holds exactly for `n = 1, 2, 4, 5, 7, 12` (all six
  are `0` in the data): the set of `n > 0` admitting no such `x, y, z` is `{1, 2, 4, 5, 7, 12}`.
-/

namespace OMA.S_oeis_a230121

theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ x y z t : ℕ, 0 < x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
        x * (x + 1) / 2 + y * (y + 1) / 2 + z * (z + 1) / 2 = t * (t + 1) / 2} = {1, 2, 4, 5, 7, 12} := by
  sorry

end OMA.S_oeis_a230121
