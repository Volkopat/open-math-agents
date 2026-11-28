import Mathlib

/-!
# A173643: Positive numbers of form 2^m - 2^l - 3*2^k (A172233) divisible by 9, divided by 9.

Source: https://oeis.org/A173643
Credit: @agchua

Comment line of A173643 (the entry is by Ralf Stephan, Nov 24 2010), verbatim:
  Conjecture: Odd part of a(n) is of form [(1/6)*(8^m-(-1)^m-3)*4^k-1]/3, k,m>0.
Offset of A173643: 1 (data 1, 2, 3, 4, 5, 6, 8, 10, 12, 13, 16, 20, 21, ...).
A172233 (by Ralf Stephan): Positive numbers of form 2^m - 2^l - 3*2^k, m>l>k>=0.

Formalisation. x is a term of A172233 if x > 0 and x = 2^m - 2^l - 3*2^k (computed in the
integers) for some natural numbers m > l > k. The terms of A173643 are the numbers x/9 for the
terms x of A172233 that are divisible by 9. The odd part of a positive integer a is the odd
number o with a = 2^e * o for some e. The conjecture says: for every such term, its odd part o
equals [(1/6)*(8^m - (-1)^m - 3)*4^k - 1]/3 (computed in the rationals) for some k > 0, m > 0.
-/

namespace OMA.S_oeis_a173643

/-- x is a term of A172233: x > 0 and x = 2^m - 2^l - 3*2^k with m > l > k >= 0. -/
def InA172233 (x : ℕ) : Prop :=
  0 < x ∧ ∃ m l k : ℕ, l < m ∧ k < l ∧ (x : ℤ) = 2 ^ m - 2 ^ l - 3 * 2 ^ k

/-- The odd part o of every term x/9 of A173643 has the form
[(1/6)*(8^m - (-1)^m - 3)*4^k - 1]/3 with k, m > 0. -/
theorem main : ∀ x e o : ℕ, InA172233 x → 9 ∣ x → x / 9 = 2 ^ e * o → Odd o →
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧
      (o : ℚ) = ((1 / 6) * ((8 : ℚ) ^ m - (-1) ^ m - 3) * 4 ^ k - 1) / 3 := by
  sorry

end OMA.S_oeis_a173643
