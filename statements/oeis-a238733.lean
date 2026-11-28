import Mathlib

/-!
# A238733: a prime p < n with floor((n-p)/m) of the form (q-1)(q-3)/8

Source: https://oeis.org/A238733
Credit: @coleman415

The entry (Zhi-Wei Sun) records: *Conjecture: (i) For any integers m > 2 and n > 2, there is a
prime p < n such that floor((n-p)/m) has the form (q-1)*(q-3)/8 with q an odd prime.*

`main` is part (i), the statement listed for this problem. Part (ii) of the entry (the form
`(q^2 - 1)/8`, for `n > m + 1`, with the exception `m = 3`, `n = 19`) is a different claim and is
not stated here.

Conventions:
- `m`, `n`, `p`, `q` are natural numbers. Since `p < n`, the natural-number subtraction `n - p`
  is the integer difference, and natural-number division by `m` is the floor.
- For an odd prime `q` we have `q ≥ 3`, so `(q - 1) * (q - 3)` is an honest product of
  natural numbers, and it is divisible by 8; the division by 8 is exact. The value `0` occurs
  (`q = 3`), as in the entry's example `floor((25-23)/3) = 0 = (3-1)*(3-3)/8`.
-/

namespace OMA.S_oeis_a238733

/-- Part (i) of the conjecture of OEIS A238733. -/
theorem main :
    ∀ m n : ℕ, 2 < m → 2 < n →
      ∃ p q : ℕ, p.Prime ∧ p < n ∧ q.Prime ∧ Odd q ∧ (n - p) / m = (q - 1) * (q - 3) / 8 := by
  sorry

end OMA.S_oeis_a238733
