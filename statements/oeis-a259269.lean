import Mathlib

/-!
# A259269: G.f. A(x) satisfies: A'(x)/2 = Series_Reversion( x - 3*A(x)^2 * A'(x)/2 ).

Source: https://oeis.org/A259269
Credit: @Luckylamb666

`A(x) = x^2 + x^6 + 12*x^10 + 264*x^14 + ... = ∑_{n ≥ 1} a(n) x^(4n - 2)` and
`G(x) = A'(x)/2` satisfy `G(x - 3 * A(x)^2 * G(x)) = x`.
Conjecture: for `n ≥ 1`, `a(n) ≡ 1 (mod 3)` iff `2*n - 1` is a power of `3`,
and `a(n) ≡ 0 (mod 3)` otherwise.
-/

namespace OMA.S_oeis_a259269

theorem main :
    ∀ (A G : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.derivative ℤ A = PowerSeries.C (2 : ℤ) * G →
      PowerSeries.subst (PowerSeries.X - PowerSeries.C (3 : ℤ) * A ^ 2 * G) G = PowerSeries.X →
      ∀ n : ℕ, 1 ≤ n →
        (PowerSeries.coeff (4 * n - 2) A % 3 = 1 ↔ ∃ k : ℕ, 2 * n - 1 = 3 ^ k) ∧
        (¬ (∃ k : ℕ, 2 * n - 1 = 3 ^ k) → PowerSeries.coeff (4 * n - 2) A % 3 = 0) := by
  sorry

end OMA.S_oeis_a259269
