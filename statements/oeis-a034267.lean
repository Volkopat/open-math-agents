import Mathlib

/-!
# A034267: Mathar's recurrence

Source: https://oeis.org/A034267
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. The
recurrence follows from the closed form of the entry, which is used as the definition here.

A034267 (offset 0): a(n) = f(n,n) where f is given in A034261;
data 0, 1, 7, 39, 196, 930, 4257, 19019, 83512, 361998, 1553630, 6615686, 27992472, ...

Conjecture (R. J. Mathar, Feb 10 2025): D-finite with recurrence
-(n+2)*(11*n-7)*a(n) + 2*(23*n^2+44*n+30)*a(n-1) - 4*(n+5)*(2*n-3)*a(n-2) = 0.

Formalization: the entry records the closed form a(n) = binomial(2*n, n+1)*(n^2+n+1)/(n+2) (Amiram
Eldar, Sep 04 2025), and this formula, read in ℚ, is the definition of a(n) used here. The recurrence
involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for example at n = 2:
(-60)*(7) + (420)*(1) + (-28)*(0) = 0.
-/

namespace OMA.S_oeis_a034267

/-- a(n) = binomial(2n, n+1)*(n^2+n+1)/(n+2), the closed form recorded in the entry. -/
def a (n : ℕ) : ℚ := ((2 * n).choose (n + 1) : ℚ) * ((n : ℚ) ^ 2 + (n : ℚ) + 1) / ((n : ℚ) + 2)

/-- Mathar's conjectured recurrence for A034267, for n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    -(((n : ℚ) + 2) * (11 * (n : ℚ) - 7)) * a n + 2 * (23 * (n : ℚ) ^ 2 + 44 * (n : ℚ) + 30) * a (n - 1) -
      4 * ((n : ℚ) + 5) * (2 * (n : ℚ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a034267
