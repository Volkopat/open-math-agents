import Mathlib

/-!
# A295431: a(n) = (12*n)!*n! / ((6*n)!*(4*n)!*(3*n)!)

Source: https://oeis.org/A295431

`a(n) = (12n)! n! / ((6n)! (4n)! (3n)!)`, offset 0 (an integral factorial ratio sequence).

Peter Bala (Jan 24 2020) notes that `a(p^k) == a(p^(k-1)) (mod p^(3k))` for primes `p >= 5`
(derived from Mestrovic) and conjectures more generally that
`a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k))` for every prime `p >= 5` and all positive integers `n`, `k`.
The case `k = 1` (`a(n*p) == a(n) (mod p^3)`) is proved in Zudilin's article (comment of Jul 30 2021);
the general statement for all `k` is the target here. The integrality conjectures of Aug 2025 and
Jun 2026 in the same entry are not part of this statement.

Formalized: `a n` is the natural-number quotient of the factorials, cast to `ℤ`; the quotient is
exact because the ratio is an integer for every `n`. The congruence is stated as divisibility of
the difference in `ℤ`, for all primes `p >= 5`, `n >= 1`, `k >= 1`.
-/

namespace OMA.S_oeis_a295431

/-- A295431: `a(n) = (12n)! n! / ((6n)! (4n)! (3n)!)`. -/
def a (n : ℕ) : ℤ :=
  (((12 * n).factorial * n.factorial /
    ((6 * n).factorial * (4 * n).factorial * (3 * n).factorial) : ℕ) : ℤ)

/-- Bala's conjecture: `a(n p^k) == a(n p^(k-1)) (mod p^(3k))` for primes `p >= 5`, `n, k >= 1`. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    ((p : ℤ) ^ (3 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a295431
