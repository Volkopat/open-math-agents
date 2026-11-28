import Mathlib

/-!
# A400454: Numbers k such that (2^k-1)*2^(k+3)+1 is a prime.

Source: https://oeis.org/A400454
Credit: @agchua

Comments of A400454 (unsigned; the entry is by Gary Wright, Sep 26 2026):
  Let N = N(k) = (2^k-1)*2^(k+3)+1, and M = A000225(k+1) = 2^(k+1)-1.
  Conjecture: If 2^((N-1)/4) == -1 (mod N), then N is prime.
Offset 1: the terms k of the sequence start at k = 1 (M is not used in the conjecture). The claim
is stated for every k >= 1. For k = 0 we would get N = 1, for which the congruence holds trivially
(any two integers are congruent modulo 1) while 1 is not prime; k = 0 is outside the entry's range.
-/

namespace OMA.S_oeis_a400454

/-- N(k) = (2^k-1)*2^(k+3)+1. -/
def N (k : ℕ) : ℕ := (2 ^ k - 1) * 2 ^ (k + 3) + 1

/-- The conjecture: for k >= 1, if 2^((N-1)/4) is congruent to -1 modulo N = N(k), then N is
prime. -/
theorem main : ∀ k : ℕ, 1 ≤ k → (2 : ℤ) ^ ((N k - 1) / 4) ≡ -1 [ZMOD (N k : ℤ)] →
    Nat.Prime (N k) := by
  sorry

end OMA.S_oeis_a400454
