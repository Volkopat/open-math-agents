import Mathlib

/-!
# A077568: a(1,n) as defined in A003148.

Source: https://oeis.org/A077568
Credit: @agchua

R. J. Mathar (May 26 2016), in the formula section of A077568:
  Conjecture: a(n) +a(n-1) -2*(2*n+1)*(n-1)*a(n-2)=0.
A003148 defines the family a(m, n) = ((2*n+2*m+1)!!/(2*m+1)) * 2F1(-n, m+1/2; m+3/2; 2) for
m, n >= 0, and A077568 is the case m = 1 (as in the Maple and Mathematica programs of the entry):
a(n) = ((2*n+3)!!/3) * 2F1(-n, 3/2; 5/2; 2). Here 2F1(a, b; c; z) is the Gauss series
Sum_{k>=0} (a)_k (b)_k / (c)_k * z^k / k!, where (x)_k is the rising factorial x (x+1) ... (x+k-1),
Mathlib's `ascPochhammer` evaluated at x; no denominator vanishes. Since (-n)_k = 0 for k > n,
the series terminates and equals its finite sum over k = 0..n, which is what `a` uses.
(2*n+3)!! is `Nat.doubleFactorial (2 * n + 3)`, and the values are taken in the rationals.
The sequence has offset 0 (a(0) = 1, a(1) = -1, a(2) = 11), and the recurrence uses a(n-2),
so the conjecture is stated for n >= 2.
-/

namespace OMA.S_oeis_a077568

/-- The k-th term of the series 2F1(-n, 3/2; 5/2; 2). -/
noncomputable def term (n k : ℕ) : ℚ :=
  (ascPochhammer ℚ k).eval (-(n : ℚ)) * (ascPochhammer ℚ k).eval (3 / 2) /
    (ascPochhammer ℚ k).eval (5 / 2) * 2 ^ k / (k.factorial : ℚ)

/-- A077568(n) = a(1, n) = ((2n+3)!!/3) * 2F1(-n, 3/2; 5/2; 2). -/
noncomputable def a (n : ℕ) : ℚ :=
  (Nat.doubleFactorial (2 * n + 3) : ℚ) / 3 * ∑ k ∈ Finset.range (n + 1), term n k

/-- Mathar's conjecture: for n >= 2, a(n) + a(n-1) - 2(2n+1)(n-1) a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n + a (n - 1) - 2 * (2 * (n : ℚ) + 1) * ((n : ℚ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a077568
