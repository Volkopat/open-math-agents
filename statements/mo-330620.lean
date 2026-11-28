import Mathlib.Algebra.Polynomial.Coeff

namespace OMA.S_mo_330620

/-- Gaussian binomial polynomials, defined by the q-Pascal recurrence. -/
noncomputable def gaussianBinomial : ℕ → ℕ → Polynomial ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, r + 1 =>
      gaussianBinomial n r + Polynomial.X ^ (r + 1) * gaussianBinomial n (r + 1)

/-- The shifted q-binomial power is coefficientwise bounded by the other power. -/
theorem main :
    ∀ (a b j k : ℕ), a ≤ b → j ≤ k →
      let shift := a * (b - a) * j * (k - j) * k / 2
      ∀ i : ℕ,
        (Polynomial.X ^ shift * gaussianBinomial (j * b) (j * a) ^ k).coeff i ≤
          (gaussianBinomial (k * b) (k * a) ^ j).coeff i := by
  sorry

end OMA.S_mo_330620
