import Mathlib

/-!
OEIS A160077: numerator of Hermite(n, 19/26), offset zero.
Source: https://oeis.org/A160077
Hermite(n, x) is the physicists' Hermite polynomial H_n, given by H_0 = 1, H_1 = 2x and
H_{n+2} = 2x H_{n+1} - 2(n+1) H_n (data: 1, 19, 23, -12407, ...). The numerator is the
signed numerator of the rational H_n(19/26) in lowest terms (`Rat.num`).
The conjecture is the D-finite recurrence a(n) - 19 a(n-1) + 338 (n-1) a(n-2) = 0, stated
by R. J. Mathar for n >= 2.
-/
namespace OMA.S_oeis_a160077

/-- The physicists' Hermite polynomial `H_n` evaluated at a rational `x`:
`H_0 = 1`, `H_1 = 2x`, `H_{n+2} = 2x H_{n+1} - 2(n+1) H_n`. -/
def hermiteAt (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => 2 * x
  | (n + 2) => 2 * x * hermiteAt x (n + 1) - 2 * ((n : ℚ) + 1) * hermiteAt x n

/-- A160077: the numerator of `H_n(19/26)`. -/
def a (n : ℕ) : ℤ := (hermiteAt (19 / 26) n).num

/-- Mathar's recurrence for A160077. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n - 19 * a (n - 1) + 338 * ((n : ℤ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a160077
