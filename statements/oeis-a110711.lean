import Mathlib

/-!
# A110711: Mathar's recurrence

Source: https://oeis.org/A110711
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A110711 (offset 1): number of linear arrangements of n blue, n red and n green items such that first
and last elements have the same color but there are no adjacent items of the same color;
data 0, 6, 42, 288, 1992, 13980, 99432, 715344, 5196336, 38056284, ...

Conjecture (R. J. Mathar, Nov 01 2015):
-(n+1)*(n-2)*a(n) + (7*n^2 - 13*n + 4)*a(n-1) + 8*(n-2)^2*a(n-2) = 0.

Formalization: the entry gives the formula a(n) = ((n-3)*A000172(n-1) + n*A000172(n))/(n+1) (Mark van
Hoeij, Jul 14 2010), where A000172(n) = Sum_{k=0..n} binomial(n,k)^3 are the Franel numbers; this
formula is used as the definition here, as a rational number (it reproduces the listed data,
a(1) = (-2*1 + 1*2)/2 = 0 and a(2) = (-1*2 + 2*10)/3 = 6). The sequence has offset 1 and the
recurrence involves a(n-2), so it is stated for n ≥ 3, where every index is at least the offset; it is
checked by the data, for example at n = 3: (-4)*(42) + (28)*(6) + (8)*(0) = 0.
-/

namespace OMA.S_oeis_a110711

/-- The Franel numbers A000172(n) = Sum_{k=0..n} binomial(n,k)^3. -/
def franel (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 3

/-- A110711 through the formula a(n) = ((n-3)*A000172(n-1) + n*A000172(n))/(n+1), for n ≥ 1. -/
def a (n : ℕ) : ℚ :=
  (((n : ℚ) - 3) * (franel (n - 1) : ℚ) + (n : ℚ) * (franel n : ℚ)) / ((n : ℚ) + 1)

/-- Mathar's conjectured recurrence for A110711, for n ≥ 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    -((n : ℚ) + 1) * ((n : ℚ) - 2) * a n + (7 * (n : ℚ) ^ 2 - 13 * (n : ℚ) + 4) * a (n - 1) +
      8 * ((n : ℚ) - 2) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a110711
