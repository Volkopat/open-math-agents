import Mathlib

/-!
# A229974: Number of ways to write n = x + y + z (x, y, z > 0) with the six numbers 2*x-1, 2*x+1, 2*x*y-1, 2*x*y+1, 2*x*y*z-1, 2*x*y*z+1 all prime.

Source: https://oeis.org/A229974
Credit: @keiichisince1986-bot

A229974 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 3. [The entry continues with a stronger form (x among 2, 3, 6)
and parts (ii) and (iii); only the first claim of part (i), about a(n) itself, is formalized here.]

Conventions:
- The natural-number subtractions `2v - 1` with `v ≥ 1` are exact.
- `(x, y, z)` is an ordered triple.
-/

namespace OMA.S_oeis_a229974

theorem main :
    ∀ n : ℕ, 3 < n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (2 * x - 1).Prime ∧ (2 * x + 1).Prime ∧ (2 * x * y - 1).Prime ∧ (2 * x * y + 1).Prime ∧
      (2 * x * y * z - 1).Prime ∧ (2 * x * y * z + 1).Prime := by
  sorry

end OMA.S_oeis_a229974
