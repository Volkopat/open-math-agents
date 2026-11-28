import Mathlib

/-!
# A103274: Number of ways of writing prime(n) in the form 2*prime(i)+prime(j).

Source: https://oeis.org/A103274
Credit: @keiichisince1986-bot

A103274 is the sequence `a(n)` named in the title. The entry states:
Marnell conjectures that a(n) > 0 for n > 3. (The entry adds: no exceptions below 10^9.)

Conventions:
- `n > 3` means `prime(n) ≥ 7` (`prime(4) = 7`); we state the conjecture for every prime `p ≥ 7`.
- `a(n) > 0` means that `p = 2q + r` for some primes `q` and `r`.
-/

namespace OMA.S_oeis_a103274

theorem main :
    ∀ p : ℕ, p.Prime → 7 ≤ p → ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ p = 2 * q + r := by
  sorry

end OMA.S_oeis_a103274
