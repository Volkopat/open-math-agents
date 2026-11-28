import Mathlib

/-!
# Squarefree solutions of `α(n) + 1 ∣ n + 1`, with `α(n)` the sum of the prime factors of `n`

Source: https://math.stackexchange.com/questions/3720724

Let `α(n) = p₁ + ⋯ + p_m` for `n = p₁^{x₁} ⋯ p_m^{x_m}` (the sum of the distinct prime factors).
Every prime is a trivial solution of `α(n) + 1 ∣ n + 1`, and infinitely many composite
non-squarefree solutions are known (`n = 2 · 3 · 5^{5m+4}`). The open question: does the
equation have infinitely many composite squarefree solutions?

`main` states the affirmative.

Formalization notes:
* The source's `α(n)` is `sopf n = ∑ p ∈ n.primeFactors, p`.
* Composite means `1 < n` and `n` not prime.
-/

namespace OMA.S_mse_3720724

/-- The sum of the distinct prime factors of `n`. -/
def sopf (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, p

/-- Infinitely many composite squarefree `n` satisfy `sopf n + 1 ∣ n + 1`. -/
theorem main : {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ Squarefree n ∧ sopf n + 1 ∣ n + 1}.Infinite := by
  sorry

end OMA.S_mse_3720724
