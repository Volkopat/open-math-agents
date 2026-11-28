import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace OMA.S_oeis_a397349

/-- OEIS A397349: L.g.f. `L(x) = ∑_{n ≥ 1} a(n)*x^n/n = log(1 + x + ∑_{n ≥ 2} 3*n/(3*n^2 - 1)*a(n)*x^n)`.
Differentiating `L'(x) * B(x) = B'(x)` gives the equivalent recurrence `a(1) = 1` and for `n ≥ 2`,
`a(n) = (3*n^2 - 1) * (a(n - 1) + ∑_{k=2}^{n-1} a(n - k) * a(k) * (3*k) / (3*k^2 - 1))`.
Conjecture: `a(n) ≡ [1, 2]` repeating `(mod 3)` for all `n ≥ 1`. -/
theorem main :
    ∀ a : ℕ → ℤ, a 1 = 1 →
      (∀ n : ℕ, 2 ≤ n →
        (a n : ℚ) = ((3 * n ^ 2 - 1 : ℕ) : ℚ) *
          ((a (n - 1) : ℚ) +
            ∑ k ∈ Finset.Icc 2 (n - 1),
              (a (n - k) : ℚ) * (a k : ℚ) * (3 * (k : ℚ)) / ((3 * k ^ 2 - 1 : ℕ) : ℚ))) →
      ∀ n : ℕ, 1 ≤ n → a n ≡ (if n % 2 = 1 then 1 else 2) [ZMOD 3] := by
  sorry

end OMA.S_oeis_a397349
