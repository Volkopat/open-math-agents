import Mathlib

/-!
# A229244: Mathar's recurrence

Source: https://oeis.org/A229244
Credit: @ivillar

Status: open conjecture (R. J. Mathar, May 23 2014); the entry records it as a conjecture and notes no proof or
verification of it.

A229244 (offset 1): number of n-permutations such that at least one cycle has size ceiling(n/2);
data 1, 1, 3, 9, 40, 200, 1260, 8820, 72576, 653184, 6652800, 73180800, ...

Conjecture (R. J. Mathar, May 23 2014):
(n+1)*a(n) +(-3*n+1)*a(n-1) -(n-2)*(n^2-2*n-1)*a(n-2) +(n-2)*(n-3)^2*a(n-3) = 0.

Formalization: the entry gives the closed forms
  for odd n,  a(2m+1) = binomial(2m+1,m+1)*m!^2,
  for even n, a(2m) = binomial(2m,m)*(m-1)!*(m!-(m-1)!) + (2m)!/(2*m^2),
and these formulas are used as the definition here (`a` below, with values in ℚ; the values are the integers
of the data for n ≥ 1, and a 0 is not used). The sequence has offset 1 and the recurrence involves a(n-3),
so it is stated for n ≥ 4, where every index is at least the offset; it is checked by the data, for example
at n = 4: (5)*(9) + (-11)*(3) + (-14)*(1) + (2)*(1) = 0, and at n = 5: (6)*(40) + (-14)*(9) + (-42)*(3) + (12)*(1) = 0.
-/

namespace OMA.S_oeis_a229244

/-- A229244 through the closed forms of the entry: a(2m+1) = binomial(2m+1,m+1)*m!^2 and
a(2m) = binomial(2m,m)*(m-1)!*(m!-(m-1)!) + (2m)!/(2*m^2), where m = floor(n/2). -/
def a (n : ℕ) : ℚ :=
  if n % 2 = 1 then (Nat.choose n (n / 2 + 1) : ℚ) * ((n / 2).factorial : ℚ) ^ 2
  else (Nat.choose n (n / 2) : ℚ) * ((n / 2 - 1).factorial : ℚ) *
      (((n / 2).factorial : ℚ) - ((n / 2 - 1).factorial : ℚ)) +
    (n.factorial : ℚ) / (2 * ((n / 2 : ℕ) : ℚ) ^ 2)

/-- Mathar's conjectured recurrence for A229244, for n ≥ 4. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 1) * a n + (-3 * (n : ℚ) + 1) * a (n - 1) -
      ((n : ℚ) - 2) * ((n : ℚ) ^ 2 - 2 * (n : ℚ) - 1) * a (n - 2) +
      ((n : ℚ) - 2) * ((n : ℚ) - 3) ^ 2 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a229244
