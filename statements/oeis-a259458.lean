import Mathlib

/-!
# A259458: a conjectured hypergeometric generating function

Source: https://oeis.org/A259458
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the closed form recorded in the entry, which is used as the definition here.

A259458 (offset 0): from higher-order arithmetic progressions;
data 18, 750, 20250, 463050, 9878400, 205752960, 4286520000, 90561240000, ...

Conjecture (R. J. Mathar, Aug 09 2015): g.f.: 18*3F1(5,5,5;3;x).

Formalization: the entry records the closed form a(n) = (n+4)!*(n+1)*(n+2)*(n+3)^2*(n+4)^2/384 (Georg
Fischer, Dec 06 2024), and this formula, read in ℚ, is the definition of a(n) used here. The
hypergeometric series is the formal power series
3F1(5,5,5;3;x) = Sum_n (5)_n*(5)_n*(5)_n/((3)_n*n!) * x^n, with (c)_n = c*(c+1)*...*(c+n-1) the rising
factorial (`rf c n` below); it has radius of convergence 0, so the conjecture is an identity of formal
power series: Sum_n a(n) x^n = Sum_n 18*(5)_n^3/((3)_n*n!) x^n.
-/

namespace OMA.S_oeis_a259458

open PowerSeries

/-- The rising factorial (c)_n = c (c+1) ... (c+n-1). -/
def rf (c : ℚ) (n : ℕ) : ℚ := ∏ i ∈ Finset.range n, (c + (i : ℚ))

/-- a(n) = (n+4)! (n+1) (n+2) (n+3)^2 (n+4)^2 / 384, the closed form recorded in the entry. -/
def a (n : ℕ) : ℚ :=
  ((n + 4).factorial : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) ^ 2 * ((n : ℚ) + 4) ^ 2 / 384

/-- The conjectured generating function 18*3F1(5,5,5;3;x) of A259458, as a formal power series. -/
theorem main : PowerSeries.mk a =
    PowerSeries.mk (fun n => 18 * rf 5 n ^ 3 / (rf 3 n * (n.factorial : ℚ))) := by
  sorry

end OMA.S_oeis_a259458
