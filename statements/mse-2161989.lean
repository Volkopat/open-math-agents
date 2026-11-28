import Mathlib

/-!
# Records of the fundamental Pell solution occur only at primes beyond 46

Source: https://math.stackexchange.com/questions/2161989

For a positive integer `n` that is not a perfect square, let `(a, b)` be the fundamental
solution of `x² - n y² = 1`, i.e. `f(n) = b` is the smallest positive integer such that
`n b² + 1` is a perfect square. Conjecture: if `s > 46` is a composite non-square number, there
is a prime `p < s` with `f(p) > f(s)`. Equivalently, apart from `10` and `46`, every record
value of `f` occurs at a prime (OEIS A033316). It has been checked for `s ≤ 10^6`.

Formalization notes:
* `f n` is the infimum of the positive `b` with `n b² + 1` a square; this set is nonempty for
  every non-square `n` (and primes are non-squares).
* For `s > 46`, "composite" is `¬ s.Prime`.
-/

namespace OMA.S_mse_2161989

/-- The least positive `b` such that `n b² + 1` is a perfect square. -/
noncomputable def f (n : ℕ) : ℕ := sInf {b : ℕ | 0 < b ∧ IsSquare (n * b ^ 2 + 1)}

/-- Every composite non-square `s > 46` has a prime `p < s` with `f p > f s`. -/
theorem main : ∀ s : ℕ, 46 < s → ¬ s.Prime → ¬ IsSquare s →
    ∃ p : ℕ, p.Prime ∧ p < s ∧ f s < f p := by
  sorry

end OMA.S_mse_2161989
