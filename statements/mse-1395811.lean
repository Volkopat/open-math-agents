import Mathlib

namespace OMA.S_mse_1395811

/-- The coefficient `φ_p(n)` of `q^n` in the formal power series
`1 / (q; q^4)_∞^p = ∏_{k=0}^∞ (1 - q^{4k+1})^{-p} = ∏_{k=0}^∞ ∑_{m=0}^∞ C(m+p-1, m) q^{(4k+1)m}`.
Since factors with `4k + 1 > n` and terms with `m > n` contribute only degrees `> n`,
this finite product equals the exact `q^n` coefficient of `1 / (q; q^4)_∞^p`. -/
noncomputable def phiCoeff (p n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n,
    ∑ m ∈ Finset.range (n + 1),
      Polynomial.C ((m + p - 1).choose m) * (Polynomial.X : Polynomial ℕ) ^ ((4 * k + 1) * m)).coeff n

theorem main :
    ∀ p : ℕ, Nat.Prime p → Odd p →
      ∀ n : ℕ, 1 ≤ n → (p ∣ phiCoeff p n ↔ ¬ p ∣ n) := by
  sorry

end OMA.S_mse_1395811
