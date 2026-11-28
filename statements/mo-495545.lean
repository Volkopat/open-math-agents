import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic

/-! Source: https://mathoverflow.net/questions/495545
Sequence: https://oeis.org/A078121 -/

open scoped BigOperators

namespace OMA.S_mo_495545

theorem main :
    ∀ T : ℕ → ℕ → ℤ,
      (∀ n, T n 0 = 1) →
      (∀ n k, n < k → T n k = 0) →
      (∀ n k, T (n + 1) (k + 1) = ∑ i ∈ Finset.range (n + 1), T n i * T i k) →
      ∀ n k, 0 < k → k < n →
        T n k = ∑ i ∈ Finset.range (n - k),
          T (n - k) i * T (k + i) (k - 1) * (1 + (-1 : ℤ) ^ (n + k + i + 1)) := by
  sorry

end OMA.S_mo_495545
