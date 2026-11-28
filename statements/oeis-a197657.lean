import Mathlib

/-!
# A197657: Mathar's recurrence

Source: https://oeis.org/A197657
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A197657 (offset 0): row sums of A194595;
data 1, 4, 22, 134, 866, 5812, 40048, 281374, 2006698, 14482064, 105527060, ...

Conjecture (R. J. Mathar, Jul 26 2014):
(n+1)^2*a(n) -3*(n+1)*(2*n+1)*a(n-1) -3*n*(5*n-7)*a(n-2) -8*(n-2)^2*a(n-3) = 0.

Formalization: the entry gives the formula a(n) = (A000172(n)+A000172(n+1))/3 (Max Alekseyev, Jul 15
2014), where A000172(n) = Sum_{k=0..n} binomial(n,k)^3 are the Franel numbers; this formula is used as
the definition here (it reproduces the listed data, a(0) = (1 + 2)/3 = 1). The recurrence involves
a(n-3), so it is stated for n ≥ 3; it is checked by the data, for example at n = 3:
(16)*(134) + (-84)*(22) + (-72)*(4) + (-8)*(1) = 0.
-/

namespace OMA.S_oeis_a197657

/-- The Franel numbers A000172(n) = Sum_{k=0..n} binomial(n,k)^3. -/
def franel (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 3

/-- A197657 through the formula a(n) = (A000172(n) + A000172(n+1))/3. -/
def a (n : ℕ) : ℚ := ((franel n : ℚ) + (franel (n + 1) : ℚ)) / 3

/-- Mathar's conjectured recurrence for A197657, for n ≥ 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 1) ^ 2 * a n - 3 * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) * a (n - 1) -
      3 * (n : ℚ) * (5 * (n : ℚ) - 7) * a (n - 2) - 8 * ((n : ℚ) - 2) ^ 2 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a197657
