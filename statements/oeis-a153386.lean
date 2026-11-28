import Mathlib

namespace OMA.S_oeis_a153386

/-- Peter Bala's conjecture (OEIS A153386, Aug 17 2022):
`∑_{n ≥ 1} 1 / F(2n) = 151 / 96 - 6 * ∑_{n ≥ 1} 1 / (F(2n) * F(2n + 4) * F(2n + 6))`,
where `F(n) = Nat.fib n` is the `n`-th Fibonacci number. -/
theorem main :
    (∑' n : ℕ, (1 : ℝ) / (Nat.fib (2 * (n + 1)) : ℝ)) =
      (151 : ℝ) / 96 -
        6 * ∑' n : ℕ,
          (1 : ℝ) /
            ((Nat.fib (2 * (n + 1)) : ℝ) *
             (Nat.fib (2 * (n + 1) + 4) : ℝ) *
             (Nat.fib (2 * (n + 1) + 6) : ℝ)) := by
  sorry

end OMA.S_oeis_a153386
