import Mathlib

/-!
# A401168: a(n) = least k such that 2*x^k/(1 + x^(2*k)) < 1/2, where x = u/(u+1) and u = 2*n*(n+1).

Source: https://oeis.org/A401168
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A401168 (Scott M. Foltz, Oct 16 2026): a(n) =
floor(log(2+sqrt(3))*(2*n^2 + 2*n + 1/2)) + 1; true for n <= 10^8.

Conventions:
* The sequence has offset 1 (data 6, 17, 33, 54, 80, 112, 149, 191, 238, 291, 349, 412, ...).
* `x n` is the real number u/(u+1) with u = 2*n*(n+1). a(n) is the least natural number k with
  2*x^k/(1 + x^(2*k)) < 1/2, stated with `IsLeast`.
* log is the natural logarithm `Real.log`, sqrt is `Real.sqrt`, and the floor of the (positive)
  real number is the natural-number floor `Nat.floor`. The statement is for n >= 1 (the offset of
  the sequence).
-/

namespace OMA.S_oeis_a401168

/-- x = u/(u+1) with u = 2*n*(n+1). -/
noncomputable def x (n : ℕ) : ℝ := (2 * (n : ℝ) * (n + 1)) / (2 * (n : ℝ) * (n + 1) + 1)

/-- The conjecture recorded in A401168. -/
theorem main : ∀ n : ℕ, 0 < n →
    IsLeast {k : ℕ | 2 * x n ^ k / (1 + x n ^ (2 * k)) < 1 / 2}
      (⌊Real.log (2 + Real.sqrt 3) * (2 * (n : ℝ) ^ 2 + 2 * n + 1 / 2)⌋₊ + 1) := by
  sorry

end OMA.S_oeis_a401168
