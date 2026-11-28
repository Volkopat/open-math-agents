import Mathlib

/-!
# A241535: every even semiprime more than 22 is a sum of two semiprimes

Source: https://oeis.org/A241535
Credit: @coleman415

The entry records: *Conjecture: every even semiprime more than 22 is a sum of two semiprimes.*

Conventions:
- A semiprime is a product of exactly two primes, not necessarily distinct (OEIS A001358).
  So the even semiprimes are the numbers `2 * p` with `p` prime, the range `2 * prime(n)` of the
  sequence.
- The two semiprimes of a representation may be equal (the entry's own data has `a(n) = 4`
  with `2 * prime(n) - 4` a semiprime, and nothing excludes `q = 2 * prime(n) - q`).
-/

namespace OMA.S_oeis_a241535

/-- `n` is a semiprime: a product of two primes, not necessarily distinct (OEIS A001358). -/
def IsSemiprime (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q

/-- The conjecture of OEIS A241535. -/
theorem main :
    ∀ n : ℕ, IsSemiprime n → Even n → 22 < n →
      ∃ a b : ℕ, IsSemiprime a ∧ IsSemiprime b ∧ n = a + b := by
  sorry

end OMA.S_oeis_a241535
