import Mathlib

/-!
# A306810: Inverse binomial transform of the continued fraction expansion of e.

Source: https://oeis.org/A306810
Credit: @JeremyDevs

Formalizes the recurrence conjectured by Colin Barker (Mar 12 2019) in OEIS A306810:
a(n) = - 7*a(n-1) - 21*a(n-2) - 33*a(n-3) - 27*a(n-4) - 9*a(n-5) for n>6.

Conventions:
* The sequence has offset 0 and is defined in the entry by
  a(n) = Sum_{k=0..n} (-1)^(n+k)*binomial(n,k)*b(k), where b(k) is the k-th term (offset 0) of
  the continued fraction expansion of e (A003417); data 2, -1, 2, -4, 7, -8, -2, 41, ...
  (EXAMPLE section: a(3) = -binomial(3,0)*2 + binomial(3,1)*1 - binomial(3,2)*2 + binomial(3,3)*1 = -4).
* The continued fraction expansion of e is 2, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, ... (A003417,
  offset 0). It is taken here through its classical explicit form (Euler; stated in the FORMULA
  section of A003417, M. F. Hasler, May 01 2013): b(0) = 2, b(3m-1) = 2m for m >= 1, and b(k) = 1
  for every other k. This is the function `b`: for k >= 1, b(k) = 2(k+1)/3 if k is congruent to
  2 modulo 3 (the division is exact) and b(k) = 1 otherwise. The fact that these are the partial
  quotients of the real number e is a known theorem and is not part of this statement.
* The recurrence is asserted for every n > 6, as in the source; all indices used are then natural
  numbers. The terms are integers.
* The generating function conjectured by Barker,
  (2 + 13*x + 37*x^2 + 55*x^3 + 42*x^4 + 14*x^5 + 2*x^6) / ((1 + x)*(1 + 3*x + 3*x^2)^2),
  is not stated separately: given the first seven terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a306810

/-- A003417 (offset 0), the continued fraction expansion of e: 2, 1, 2, 1, 1, 4, 1, 1, 6, ... -/
def b : ℕ → ℕ
  | 0 => 2
  | k + 1 => if (k + 1) % 3 = 2 then 2 * (k + 2) / 3 else 1

/-- A306810 (offset 0): a(n) = Sum_{k=0..n} (-1)^(n+k)*binomial(n,k)*b(k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n + k) * (n.choose k : ℤ) * (b k : ℤ)

/-- The recurrence conjectured by Barker, for every `n > 6`. -/
theorem main : ∀ n : ℕ, 6 < n →
    a n = -7 * a (n - 1) - 21 * a (n - 2) - 33 * a (n - 3) - 27 * a (n - 4) - 9 * a (n - 5) := by
  sorry

end OMA.S_oeis_a306810
