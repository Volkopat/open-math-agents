import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a203470

/-- OEIS A000178: superfactorial `∏_{k=1}^{m} k!`. -/
def superfactorial (m : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 m, k.factorial

/-- OEIS A203470: `a(n) = ∏_{2 ≤ i < j ≤ n + 1} (i + j)`. -/
def a203470 (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 2 (n + 1), ∏ i ∈ Finset.Ico 2 j, (i + j)

/-- OEIS A203470 conjectures:
1. Each term divides its successor: `a(n) ∣ a(n + 1)` for all `n ≥ 1`.
2. Each term `a(n)` is divisible by the corresponding superfactorial `A000178(n - 1)`
   (as in `A203471(n) = A203470(n) / A000178(n - 1)`). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a203470 n ∣ a203470 (n + 1)) ∧
    (∀ n : ℕ, 1 ≤ n → superfactorial (n - 1) ∣ a203470 n) := by
  sorry

end OMA.S_oeis_a203470
