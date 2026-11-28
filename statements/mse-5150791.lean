import Mathlib

/-!
# Is every prime `P ≥ 5` of the form `ab + c − 1` with `a, b, c` prime?

Source: https://math.stackexchange.com/questions/5150791
(Marnell's prime + semiprime conjecture for `n = P + 1`).
Credit: @prasledi

The statement is the Conjecture of the post: for every prime `P ≥ 5` there are primes
`a, b, c` (not necessarily distinct) with `P = a * b + c - 1`.

Formalization notes:
* All quantities are natural numbers. Since `c` is prime, `c ≥ 2`, so the natural-number
  subtraction `a * b + c - 1` is the usual one (equivalently `P + 1 = a * b + c`).
* `a`, `b`, `c` need not be distinct, as in the source.
* The further questions of the post (almost-all results, the parity problem, other variants) are
  not part of this statement.
-/

namespace OMA.S_mse_5150791

/-- Every prime `P ≥ 5` is `a * b + c - 1` for some primes `a`, `b`, `c`. -/
theorem main :
    ∀ P : ℕ, P.Prime → 5 ≤ P →
      ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ P = a * b + c - 1 := by
  sorry

end OMA.S_mse_5150791
