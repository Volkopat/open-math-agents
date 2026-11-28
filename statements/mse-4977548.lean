import Mathlib

/-!
# Every non-zero integer is the difference of a semiprime and a prime

Source: https://math.stackexchange.com/questions/4977548
Credit: @prasledi

The Conjecture of the post: every non-zero integer `n` can be written as `n = q - p`, where `q` is
a semiprime (the product of two primes, not necessarily distinct) and `p` is a prime.

Formalization notes:
* `n` ranges over all non-zero integers, negative ones included, as in the source
  (`n = 0` is excluded by the source).
* The semiprime `q` is written directly as a product `r * s` of two primes `r`, `s`, which may be
  equal, exactly as the source defines it. The difference is taken in `ℤ`.
-/

namespace OMA.S_mse_4977548

/-- Every non-zero integer is a semiprime minus a prime. -/
theorem main :
    ∀ n : ℤ, n ≠ 0 →
      ∃ r s p : ℕ, r.Prime ∧ s.Prime ∧ p.Prime ∧ n = ((r * s : ℕ) : ℤ) - (p : ℤ) := by
  sorry

end OMA.S_mse_4977548
