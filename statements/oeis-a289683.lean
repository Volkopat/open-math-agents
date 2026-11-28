import Mathlib

/-!
# A289683: Mixing moments of the busy period of mean steady-state 1/2 in an M/M/1 waiting process.

Source: https://oeis.org/A289683
Credit: @agchua

R. J. Mathar (Jul 09 2017), in the formula section of A289683:
  Conjecture: a(n) +2*(-2*n+3)*a(n-1) +(n-1)*(n-3)*a(n-2)=0.
The sequence is given in its formula section (from J. Abate and W. Whitt, Integer Sequences
from Queueing Theory, J. Int. Seq. 13 (2010), Eq. 15) by
  a(n) = n!*b(n) where b(0)=1 and
  b(n) = Sum_{k=0..n-1} binomial(n-1+k, n-1-k) *A000108(k) *(1/2)^k,
which is the definition used here; it reproduces all listed terms 1, 1, 3, 18, 171, 2250, ...
A000108(k) is Mathlib's `catalan k` (the Catalan numbers). In the sum 0 <= k <= n-1, so the
natural-number subtraction n - 1 - k is exact. Values are taken in the rationals.
The offset is 0 and the recurrence uses a(n-2), so the conjecture is stated for n >= 2.
-/

namespace OMA.S_oeis_a289683

/-- b(0) = 1 and b(n) = Sum_{k=0..n-1} binomial(n-1+k, n-1-k) * A000108(k) * (1/2)^k. -/
def b (n : ℕ) : ℚ :=
  if n = 0 then 1
  else ∑ k ∈ Finset.range n,
    ((n - 1 + k).choose (n - 1 - k) : ℚ) * (catalan k : ℚ) * (1 / 2) ^ k

/-- A289683(n) = n! * b(n). -/
def a (n : ℕ) : ℚ := (n.factorial : ℚ) * b n

/-- Mathar's conjecture: for n >= 2, a(n) + 2(-2n+3) a(n-1) + (n-1)(n-3) a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n + 2 * (-2 * (n : ℚ) + 3) * a (n - 1) + ((n : ℚ) - 1) * ((n : ℚ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a289683
