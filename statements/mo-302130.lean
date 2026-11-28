import Mathlib

/-!
# Does `n²` divide `det[(i+j)^n]_{0≤i,j≤n-1}` for each integer `n > 2`?

Source: https://mathoverflow.net/questions/302130 (Zhi-Wei Sun, CC BY-SA 4.0).

For `n = 1, 2, 3, …` let `a(n) = det[(i+j)^n]_{0 ≤ i,j ≤ n-1}`. Question: is `n² ∣ a(n)` for all
`n ≥ 3`? (The asker even conjectures that `(-1)^{n(n-1)/2} a(n) / ((n-2)! n ∏_{k=1}^n k!)` is a
positive integer for every `n > 2`; that stronger form is not stated here.)

We state the affirmative answer to the question.

Formalization notes:
* `a n` is the determinant of the `n × n` integer matrix with entries `(i + j) ^ n`,
  `0 ≤ i, j ≤ n - 1`.
* Checked numerically (exact integer determinants): `n² ∣ a(n)` for `3 ≤ n ≤ 25`.
-/

namespace OMA.S_mo_302130

/-- `a(n) = det[(i+j)^n]_{0 ≤ i,j ≤ n-1}`. -/
def a (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => ((i : ℤ) + j) ^ n)

/-- For every `n ≥ 3`, `n²` divides `det[(i+j)^n]_{0 ≤ i,j ≤ n-1}`. -/
theorem main : ∀ n : ℕ, 3 ≤ n → (n : ℤ) ^ 2 ∣ a n := by
  sorry

end OMA.S_mo_302130
