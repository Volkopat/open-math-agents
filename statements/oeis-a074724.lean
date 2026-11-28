import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace OMA.S_oeis_a074724

open ArithmeticFunction

/-- `A074724(n)` is the highest power of `3` dividing `F(4 * n)`, i.e., `3 ^ padicValNat 3 (Nat.fib (4 * n))`. -/
noncomputable def a074724 (n : ℕ) : ℕ :=
  3 ^ padicValNat 3 (Nat.fib (4 * n))

/-- OEIS A074724 conjectures (Michel Marcus, May 17 2022; Peter Bala, Jun 10 2022):
for every `n ≥ 1`,
1. `A074724(n) = 3 ^ (padicValNat 3 n + 1)` (i.e. `3 ^ A051064(n)`), and
2. `A074724(n) * (σ(3 * n) - 3 * σ(n)) = σ(3 * n) - σ(n)` (with `3 * σ(n) < σ(3 * n)`),
where `σ = ArithmeticFunction.sigma 1` is the sum-of-divisors function. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      a074724 n = 3 ^ (padicValNat 3 n + 1) ∧
      3 * sigma 1 n < sigma 1 (3 * n) ∧
      a074724 n * (sigma 1 (3 * n) - 3 * sigma 1 n) = sigma 1 (3 * n) - sigma 1 n := by
  sorry

end OMA.S_oeis_a074724
