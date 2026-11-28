import Mathlib

/-!
# A075045: Alcover's recurrence

Source: https://oeis.org/A075045
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A075045 (offset 0): coefficients A_n for the s=3 tennis ball problem;
data 1, 9, 69, 502, 3564, 24960, 173325, 1196748, 8229849, 56427177, ...

Conjecture (Jean-François Alcover, Feb 07 2019): D-finite with recurrence
8*(2*n+3)*(7*n+1)*(n+1)*a(n) +6*(-252*n^3-477*n^2-220*n-11)*a(n-1) +81*(7*n+8)*(3*n-1)*(3*n+1)*a(n-2) = 0.

Formalization: the entry gives the formula a(n) = Sum_{k=0..n} 2^(n-k) * binomial(3*n+4,k) (Seiichi
Manyama, Jul 28 2025), and this formula is used as the definition here (it reproduces the listed
data, a(0) = 1, a(1) = 2 + 7 = 9, a(2) = 4 + 20 + 45 = 69). The recurrence involves a(n-2), so it is
stated for n ≥ 2; it is checked by the data, for example at n = 2:
(2520)*(69) + (-26250)*(9) + (62370)*(1) = 0.
-/

namespace OMA.S_oeis_a075045

/-- A075045 through the formula a(n) = Sum_{k=0..n} 2^(n-k) * binomial(3*n+4,k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), 2 ^ (n - k) * ((3 * n + 4).choose k : ℤ)

/-- Alcover's conjectured recurrence for A075045, for n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    8 * (2 * (n : ℤ) + 3) * (7 * (n : ℤ) + 1) * ((n : ℤ) + 1) * a n +
      6 * (-252 * (n : ℤ) ^ 3 - 477 * (n : ℤ) ^ 2 - 220 * (n : ℤ) - 11) * a (n - 1) +
      81 * (7 * (n : ℤ) + 8) * (3 * (n : ℤ) - 1) * (3 * (n : ℤ) + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a075045
