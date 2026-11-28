import Mathlib

/-!
# A242207: primitive prime divisors of Domb numbers

Source: https://oeis.org/A242207
Credit: @coleman415

The sequence (Zhi-Wei Sun) is: `a(n)` = least prime divisor of the `n`-th Domb number `D(n)` which
does not divide any `D(k)` with `k < n`, or `1` if such a primitive prime divisor of `D(n)` does
not exist. The sequence has offset 1.
The entry records: *Conjecture: a(n) is prime except for n = 3.*

So the conjecture says: for `n ≥ 1`, a prime divisor of `D(n)` that divides no `D(k)` with
`0 < k < n` exists exactly when `n ≠ 3`.

Conventions:
- The Domb numbers (OEIS A002895) are
  `D(n) = sum_{k=0..n} binomial(n,k)^2 * binomial(2k,k) * binomial(2(n-k),n-k)`:
  1, 4, 28, 256, 2716, ... (the entry's example: `D(1) = 2^2`, `D(2) = 2^2*7`, `D(3) = 2^8`,
  `D(4) = 2^2*7*97`).
- `k` ranges over `0 < k < n`, the indices of the sequence, as in the entry's example for
  `a(4)`, which lists `D(1)`, `D(2)`, `D(3)`. (`D(0) = 1` has no prime divisor, so allowing
  `k = 0` changes nothing.)
-/

namespace OMA.S_oeis_a242207

/-- The `n`-th Domb number (OEIS A002895). -/
def domb (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (2 * k).choose k * (2 * (n - k)).choose (n - k)

/-- The conjecture of OEIS A242207. -/
theorem main :
    ∀ n : ℕ, 0 < n →
      ((∃ p : ℕ, p.Prime ∧ p ∣ domb n ∧ ∀ k : ℕ, 0 < k → k < n → ¬ p ∣ domb k) ↔ n ≠ 3) := by
  sorry

end OMA.S_oeis_a242207
