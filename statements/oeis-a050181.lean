import Mathlib

/-!
# A050181: T(2n+3, n), array T as in A051168; a count of Lyndon words.

Source: https://oeis.org/A050181
Credit: @agchua

R. J. Mathar (Jul 20 2016), in the formula section of A050181:
  Conjecture: -(n-1)*(n+3)*(n+2)*a(n) + 2*(3*n-4)*(n+2)*(n+1)*a(n-1) - 4*n*(n+1)*(2*n-5)*a(n-2)
  + 2*(n-1)*(n+2)*(2*n-3)*a(n-3) - 4*(2*n-5)*(3*n-4)*(n+1)*a(n-4) + 8*n*(2*n-5)*(2*n-7)*a(n-5) = 0.
A051168 is the triangle T(h,k) = number of binary Lyndon words with k ones and h-k zeros, with
A. Howroyd's formula T(h,k) = (1/h) * Sum_{d | gcd(h,k)} mu(d) * binomial(h/d, k/d) for h > 0 (from
the formula section of A051168); mu is the Moebius function (Mathlib: ArithmeticFunction.moebius).
The definition below is this formula, and a(n) = T(2n+3, n) as in the name line. P. Hadjicostas
(Nov 16 2017) writes in the entry that a(n) = (1/(2n+3)) * Sum_{d | gcd(n,3)} mu(d) * binomial((2n+3)/d, n/d)
and that with these formulae one can verify Mathar's conjecture. The values are taken in the
rationals (they are integers). The sequence has offset 0 (a(0) = 0, a(1) = 1, a(2) = 3). The
recurrence uses a(n-5), so the conjecture is stated for n >= 5.
-/

namespace OMA.S_oeis_a050181

/-- T(h,k) of A051168 by A. Howroyd's formula: (1/h) Sum_{d | gcd(h,k)} mu(d) binomial(h/d, k/d). -/
noncomputable def T (h k : ℕ) : ℚ :=
  (1 / (h : ℚ)) * ∑ d ∈ (Nat.gcd h k).divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℚ) * ((h / d).choose (k / d) : ℚ)

/-- A050181(n) = T(2n+3, n). -/
noncomputable def a (n : ℕ) : ℚ := T (2 * n + 3) n

/-- Mathar's conjecture, for n >= 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    -((n : ℚ) - 1) * ((n : ℚ) + 3) * ((n : ℚ) + 2) * a n
      + 2 * (3 * (n : ℚ) - 4) * ((n : ℚ) + 2) * ((n : ℚ) + 1) * a (n - 1)
      - 4 * (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) - 5) * a (n - 2)
      + 2 * ((n : ℚ) - 1) * ((n : ℚ) + 2) * (2 * (n : ℚ) - 3) * a (n - 3)
      - 4 * (2 * (n : ℚ) - 5) * (3 * (n : ℚ) - 4) * ((n : ℚ) + 1) * a (n - 4)
      + 8 * (n : ℚ) * (2 * (n : ℚ) - 5) * (2 * (n : ℚ) - 7) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a050181
