import Mathlib

/-!
# A144652: Triangle, read by rows, where T(m,n) = floor((2mn+m+n)/2) with m >= n >= 1.

Source: https://oeis.org/A144652
Credit: @agchua

Comment of A144652 (from Vincenzo Librandi, Nov 16 2012):
  Conjecture: If h does not belong to the sequence, then 4*h+1 is prime.
The terms of the sequence are the values T(m,n) = floor((2mn+m+n)/2) with m >= n >= 1 (offset 1,1);
the floor of a quotient of natural numbers is the natural division. The claim is stated literally
for every positive integer h (the terms are positive integers). The value h = 0 is left out: it is
not a term (every term is at least 2), and 4*0+1 = 1 is not prime.
-/

namespace OMA.S_oeis_a144652

/-- T(m,n) = floor((2mn+m+n)/2). -/
def T (m n : ℕ) : ℕ := (2 * m * n + m + n) / 2

/-- Librandi's conjecture: if a positive integer h is not a value T(m,n) with m >= n >= 1, then
4h+1 is prime. -/
theorem main : ∀ h : ℕ, 1 ≤ h →
    (¬ ∃ m n : ℕ, 1 ≤ n ∧ n ≤ m ∧ T m n = h) → Nat.Prime (4 * h + 1) := by
  sorry

end OMA.S_oeis_a144652
