import Mathlib

/-!
# A110707: Mathar's recurrence

Source: https://oeis.org/A110707
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A110707 (offset 1): number of linear arrangements of n blue, n red and n green items such that there
are no adjacent items of the same color (first and last elements considered as adjacent);
data 6, 24, 132, 804, 5196, 34872, 240288, 1688244, 12040188, 86892384, ...

Conjecture (R. J. Mathar, Jul 26 2014):
n^2*a(n) -3*n*(2*n-1)*a(n-1) -3*(n-1)*(5*n-12)*a(n-2) -8*(n-3)^2*a(n-3) = 0.

Formalization: the entry gives the formula a(n) = 2*A000172(n-1)+2*A000172(n) (Mark van Hoeij, Jul 14
2010), where A000172(n) = Sum_{k=0..n} binomial(n,k)^3 are the Franel numbers; this formula is used as
the definition here (it reproduces the listed data, a(1) = 2*1 + 2*2 = 6). The sequence has offset 1
and the recurrence involves a(n-3), so it is stated for n ≥ 4, where every index is at least the
offset; it is checked by the data, for example at n = 4:
(16)*(804) + (-84)*(132) + (-72)*(24) + (-8)*(6) = 0.
-/

namespace OMA.S_oeis_a110707

/-- The Franel numbers A000172(n) = Sum_{k=0..n} binomial(n,k)^3. -/
def franel (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 3

/-- A110707 through the formula a(n) = 2*A000172(n-1) + 2*A000172(n), for n ≥ 1. -/
def a (n : ℕ) : ℤ := 2 * (franel (n - 1) : ℤ) + 2 * (franel n : ℤ)

/-- Mathar's conjectured recurrence for A110707, for n ≥ 4. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℤ) ^ 2 * a n - 3 * (n : ℤ) * (2 * (n : ℤ) - 1) * a (n - 1) -
      3 * ((n : ℤ) - 1) * (5 * (n : ℤ) - 12) * a (n - 2) - 8 * ((n : ℤ) - 3) ^ 2 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a110707
