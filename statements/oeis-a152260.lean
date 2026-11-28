import Mathlib

namespace OMA.S_oeis_a152260

open PowerSeries BigOperators

/-- Stirling numbers of the second kind `S2(n, k)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- The formal power series `x * p(n, x) = (1 / n) * (1 - x)^(2 * n) * ∑_{j ≥ 0} C(n + j - 1, j) * j^n * x^j`
whose `x^m` coefficient (`1 ≤ m ≤ n`) is the `(n, m)` entry `T(n, m)` of OEIS A152260. -/
noncomputable def a152260Series (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.C ((n : ℚ)⁻¹) * (1 - PowerSeries.X) ^ (2 * n) *
    PowerSeries.mk fun j => (Nat.choose (n + j - 1) j : ℚ) * (j : ℚ) ^ n

/-- The `(n, m)` entry of OEIS A152260 (`1 ≤ m ≤ n`), equal to `[x^(m-1)] p(n, x) = [x^m] (x * p(n, x))`. -/
noncomputable def a152260 (n m : ℕ) : ℚ :=
  PowerSeries.coeff m (a152260Series n)

/-- Conjecture on OEIS A152260:
for all `n ≥ 1` and `1 ≤ m ≤ n`,
`T(n, m) = ∑_{k=1}^m C(n + k, k) * C(n - k, m - k) * k! * (-1)^(m - k) * S2(n, k) / (n + k)`. -/
theorem main :
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ n →
      a152260 n m =
        ∑ k ∈ Finset.Icc 1 m,
          (Nat.choose (n + k) k : ℚ) * (Nat.choose (n - k) (m - k) : ℚ) *
            (Nat.factorial k : ℚ) * (-1 : ℚ) ^ (m - k) * (stirling2 n k : ℚ) /
            ((n + k : ℕ) : ℚ) := by
  sorry

end OMA.S_oeis_a152260
