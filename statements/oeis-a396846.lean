import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace OMA.S_oeis_a396846

/-- OEIS A396846: L.g.f. `L(x) = ∑_{n ≥ 1} a(n)*x^n/n = log(1 + x + ∑_{n ≥ 2} 4*n/(4*n^2 - 1)*a(n)*x^n)`.
Differentiating `L'(x) * B(x) = B'(x)` gives the equivalent recurrence `a(1) = 1` and for `n ≥ 2`,
`a(n) = (4*n^2 - 1) * (a(n - 1) + ∑_{k=2}^{n-1} a(n - k) * a(k) * (4*k) / (4*k^2 - 1))`.
Conjecture: `a(n) ≡ [1, 7, 5, 7]` repeating `(mod 8)` for all `n ≥ 1`. -/
theorem main :
    ∀ a : ℕ → ℤ, a 1 = 1 →
      (∀ n : ℕ, 2 ≤ n →
        (a n : ℚ) = ((4 * n ^ 2 - 1 : ℕ) : ℚ) *
          ((a (n - 1) : ℚ) +
            ∑ k ∈ Finset.Icc 2 (n - 1),
              (a (n - k) : ℚ) * (a k : ℚ) * (4 * (k : ℚ)) / ((4 * k ^ 2 - 1 : ℕ) : ℚ))) →
      ∀ n : ℕ, 1 ≤ n →
        a n ≡ (if n % 4 = 1 then 1 else if n % 4 = 3 then 5 else 7) [ZMOD 8] := by
  sorry

end OMA.S_oeis_a396846
