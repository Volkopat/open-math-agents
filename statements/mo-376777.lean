import Mathlib

/-!
# Are the numbers `φ(n²)σ(n²)` (n = 1, 2, 3, ...) pairwise distinct?

Source: https://mathoverflow.net/questions/376777
Credit: @JeremyDevs

Question (Zhi-Wei Sun, MathOverflow 376777, 2020). Let `φ` be the Euler totient function and
`σ(n) = ∑_{d ∣ n} d`.
Question 1. Are the numbers `φ(n²)σ(n²)` (`n = 1, 2, 3, ...`) pairwise distinct?
Question 2. Are the rationals `σ(n²)/φ(n²)` (`n = 1, 2, 3, ...`) pairwise distinct?
The author conjectures "that the answers to both questions are affirmative" (verified for
`n ≤ 10^7`). `main` is this conjecture: the conjunction of the two affirmative answers.

Conventions:
* `φ` is `Nat.totient`, `σ` is `ArithmeticFunction.sigma 1` (sum of the positive divisors).
* `n = 1, 2, 3, ...` is `n : ℕ` with `0 < n`; "pairwise distinct" is stated as injectivity:
  equal values force equal indices.
* The quotient in Question 2 is taken in `ℚ` (the source says "the rationals"); `φ(n²) > 0`
  for `n ≥ 1`, so there is no division by zero.
-/

namespace OMA.S_mo_376777

open ArithmeticFunction in
/-- Both sequences `φ(n²)σ(n²)` and `σ(n²)/φ(n²)`, `n ≥ 1`, are injective. -/
theorem main :
    (∀ m n : ℕ, 0 < m → 0 < n →
      Nat.totient (m ^ 2) * sigma 1 (m ^ 2) = Nat.totient (n ^ 2) * sigma 1 (n ^ 2) → m = n) ∧
    (∀ m n : ℕ, 0 < m → 0 < n →
      (sigma 1 (m ^ 2) : ℚ) / (Nat.totient (m ^ 2) : ℚ) =
        (sigma 1 (n ^ 2) : ℚ) / (Nat.totient (n ^ 2) : ℚ) → m = n) := by
  sorry

end OMA.S_mo_376777
