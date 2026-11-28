import Mathlib

/-!
# A123922: Mathar's recurrence

Source: https://oeis.org/A123922
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Jan 25 2013); the entry records it as a conjecture and notes no proof or
verification of it.

A123922 (offset 0): number of 2143-avoiding Dumont paths of the 2nd kind of length 2n;
data 1, 1, 2, 6, 21, 84, 360, 1650, 7865, 39039, 198744, 1039584, ...

Conjecture (R. J. Mathar, Jan 25 2013):
16*n*(n+2)*(n+1)^2*a(n) -108*n*(n+1)*(2*n-1)*a(n-1) -9*(3*n-5)*(3*n-1)*(3*n-4)*(3*n-2)*a(n-2) = 0.

Formalization: the entry gives the formula a(n) = A047749(n)*A047749(n+1), and this formula is used as the
definition here. A047749 is defined in its own entry by: if n = 2*m then b(n) = binomial(3*m, m)/(2*m+1), and
if n = 2*m+1 then b(n) = binomial(3*m+1, m+1)/(2*m+1); `b` below is this definition, with the quotient
taken in ℚ (the values are integers: 1, 1, 1, 2, 3, 7, 12, 30, 55, 143, ...). The recurrence involves
a(n-2), so it is stated for n ≥ 2; it is checked by the data, for example at n = 2:
(1152)*(2) + (-1944)*(1) + (-360)*(1) = 0, and at n = 3: (3840)*(6) + (-6480)*(2) + (-10080)*(1) = 0.
-/

namespace OMA.S_oeis_a123922

/-- A047749: b(2m) = binomial(3m, m)/(2m+1) and b(2m+1) = binomial(3m+1, m+1)/(2m+1). -/
def b (n : ℕ) : ℚ :=
  if n % 2 = 0 then (Nat.choose (3 * (n / 2)) (n / 2) : ℚ) / (2 * ((n / 2 : ℕ) : ℚ) + 1)
  else (Nat.choose (3 * (n / 2) + 1) (n / 2 + 1) : ℚ) / (2 * ((n / 2 : ℕ) : ℚ) + 1)

/-- A123922 through the formula of the entry: a(n) = A047749(n) * A047749(n+1). -/
def a (n : ℕ) : ℚ := b n * b (n + 1)

/-- Mathar's conjectured recurrence for A123922, for n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    16 * (n : ℚ) * ((n : ℚ) + 2) * ((n : ℚ) + 1) ^ 2 * a n -
      108 * (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) - 1) * a (n - 1) -
      9 * (3 * (n : ℚ) - 5) * (3 * (n : ℚ) - 1) * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a123922
