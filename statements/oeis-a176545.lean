import Mathlib

/-!
# OEIS A176545: Numbers `k > 0` such that `2 * k ^ 2 + 14 * k + 5` is prime

Source: https://oeis.org/A176545
Credit: @itsrainingmani (implementation: Gemini 4 Neon via Antigravity)
Secondary: https://lefttosolve.com/p/oeis-a176545

OEIS A176545 (Vincenzo Librandi, Apr 20 2010) is the sequence of positive integers `k > 0`
such that `p = 2 * k ^ 2 + 14 * k + 5` is prime (beginning `2, 9, 11, 12, 14, 17, ...`).
The case `k = 0` yields `p = 5` and `2 ^ 5 - 1 = 31` (prime), and is excluded by `k > 0`.

Comment on OEIS A176545:
"Conjecture: If p = 2*k^2 + 14*k + 5 then 2^p - 1 is not prime."

Since `k` ranges over A176545 (`k > 0` with `2 * k ^ 2 + 14 * k + 5` prime), we state the
conjecture for all `k : ℕ` with `0 < k` and `(2 * k ^ 2 + 14 * k + 5).Prime`. (Note that this
is also logically equivalent to dropping the primality hypothesis on `2 * k ^ 2 + 14 * k + 5`,
because whenever `2 ^ p - 1` is prime, `p` must itself be prime.)
-/

namespace OMA.S_oeis_a176545

/-- Conjecture from OEIS A176545: for every `k > 0` such that `p = 2 * k ^ 2 + 14 * k + 5` is
prime, the Mersenne number `2 ^ p - 1` is not prime. -/
theorem main :
    ∀ k : ℕ, 0 < k → (2 * k ^ 2 + 14 * k + 5).Prime →
      ¬ (2 ^ (2 * k ^ 2 + 14 * k + 5) - 1).Prime := by
  sorry

end OMA.S_oeis_a176545
