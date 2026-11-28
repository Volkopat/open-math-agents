import Mathlib.Data.Int.Basic

/-!
# The printed recurrence for OEIS A168494

The OEIS gives the Stieltjes continued fraction with successive numerators
`x, x, 3*x`, repeated. Its coefficient of degree `n` counts excursions of
length `2*n` on the nonnegative integers, with each down-step from height
`h` weighted by the `h`-th numerator coefficient. Indeed, splitting at the
first return gives the tail series `F_h = 1/(1 - w_(h+1) * x * F_(h+1))`.
The recursion below computes these coefficients directly from the walks.

R. J. Mathar's formula prints `a(n-2)` twice. Both terms are transcribed as
printed. The sequence has offset zero, so all four backward shifts exist
for `n ≥ 4`.

Source: https://oeis.org/A168494
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a168494

def weight (h : ℕ) : ℕ := if h % 3 = 0 then 3 else 1

/-- Total weight of nonnegative walks from `h` to zero in the given number of steps. -/
def walks : ℕ → ℕ → ℕ
  | 0, h => if h = 0 then 1 else 0
  | t + 1, 0 => walks t 1
  | t + 1, h + 1 => walks t (h + 2) + weight (h + 1) * walks t h

def a (n : ℕ) : ℤ := walks (2 * n) 0

theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + (4 - 11 * (n : ℤ)) * a (n - 2) +
    5 * (7 * (n : ℤ) - 11) * a (n - 2) + (92 - 37 * (n : ℤ)) * a (n - 3) +
    6 * (2 * (n : ℤ) - 7) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a168494
