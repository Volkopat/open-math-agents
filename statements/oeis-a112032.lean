import Mathlib

/-!
# A112032: Denominator of 3/4 + 1/4 - 3/8 - 1/8 + 3/16 + 1/16 - 3/32 - 1/32 + 3/64 ...

Source: https://oeis.org/A112032
Credit: @ivillar

Reinhard Zumkeller's sequence (offset 0): a(n) is the denominator (in lowest terms) of the
partial sum of the first n+1 terms of the series 3/4 + 1/4 - 3/8 - 1/8 + 3/16 + 1/16 - ...,
whose k-th term (k ≥ 0) is (-1)^floor(k/2) * (3 if k is even, 1 if k is odd) / 2^(floor(k/2)+2)
(the comment of A112032: partial sums of A112030(k)/A016116(k+4)). So a(0) = 4 (3/4),
a(1) = 1 (3/4 + 1/4 = 1), a(2) = 8 (5/8), a(3) = 2 (1/2), ...

Conjectures from Colin Barker, Apr 05 2013:
  a(n) = 2*a(n-2) (for n ≥ 2), and
  G.f.: (x+4) / (1-2*x^2), taken as a formal power series over ℚ.
-/

namespace OMA.S_oeis_a112032

open PowerSeries

/-- The k-th term of 3/4 + 1/4 - 3/8 - 1/8 + 3/16 + 1/16 - ... (k ≥ 0). -/
def c (k : ℕ) : ℚ := (-1) ^ (k / 2) * (if Even k then 3 else 1) / 2 ^ (k / 2 + 2)

/-- The sum of the first n+1 terms. -/
def s (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), c k

/-- a(n): the denominator of the n-th partial sum. -/
def a (n : ℕ) : ℕ := (s n).den

/-- Barker's conjectures: the recurrence and the generating function. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → a n = 2 * a (n - 2)) ∧
    mk (fun n => (a n : ℚ)) = (X + 4) * (1 - 2 * X ^ 2)⁻¹ := by
  sorry

end OMA.S_oeis_a112032
