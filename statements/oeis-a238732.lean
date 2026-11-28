import Mathlib

/-!
# A238732: a prime p < n with floor((n-p)/m) a square

Source: https://oeis.org/A238732
Credit: @coleman415

The entry (Zhi-Wei Sun) records: *Conjecture: (i) For any integers m > 2 and n > 2, there is a
prime p < n such that floor((n-p)/m) is a square.*

`main` is part (i), the statement listed for this problem. Part (ii) of the entry (k-th powers,
for m and n sufficiently large) is a different claim and is not stated here.

Conventions:
- `0` counts as a square (the entry's example: `a(3) = 1` since `floor((3-2)/3) = 0^2`).
- `m` and `n` are natural numbers. Since `p < n`, the natural-number subtraction `n - p` is the
  integer difference, and natural-number division is the floor.
-/

namespace OMA.S_oeis_a238732

/-- Part (i) of the conjecture of OEIS A238732. -/
theorem main :
    ∀ m n : ℕ, 2 < m → 2 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ IsSquare ((n - p) / m) := by
  sorry

end OMA.S_oeis_a238732
