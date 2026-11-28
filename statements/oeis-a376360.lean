import Mathlib

/-!
# A376360: Positions of numbers in A007961 that end in 3.

Source: https://oeis.org/A376360
Credit: @agchua

Comment line of A376360 (Clark Kimberling, Sep 25 2024), verbatim:
  Conjecture: {a(n+1) - a(n) : n >= 1} = {4,5,6,7,8,9,10,11,13}. It has been checked that a(n+1) - a(n) is not 12 for 1<=n<=300000.  (See related conjectures at A376357, A376358, and A376359.)
Offset of A376360: 1 (data 3, 7, 12, 19, 23, 28, 32, 39, ...).

A007961 (offset 1) is n written in base where place values are positive squares. As in the
entry's Maple program (R. J. Mathar), with k = floor(sqrt(n)) the digits are computed greedily
for the place values k^2, (k-1)^2, ..., 1^2: the digit of b^2 is floor(r/b^2) for the current
remainder r, the remainder then becomes r mod b^2, and the digit of b^2 is written at the decimal
position b-1 (units for b = 1). So A007961(n) = rep(n, floor(sqrt(n))) with rep as below; for
example A007961(3) = 3, A007961(7) = 13, and A007961(12) = 103.
A376360 lists the n >= 1 such that A007961(n) ends in 3 (A007961(n) mod 10 = 3) in increasing
order, so a(n) is Nat.nth of that predicate at n - 1 (Nat.nth counts from 0). The conjecture says
that the set of the differences a(n+1) - a(n), n >= 1, is exactly {4, 5, 6, 7, 8, 9, 10, 11, 13}.
The remark about 1<=n<=300000 is a computational check note (and is implied by the set equality).
-/

namespace OMA.S_oeis_a376360

/-- rep r b: r written greedily with the place values b^2, (b-1)^2, ..., 1^2, read as a decimal
number; the digit of b^2 stands at the decimal position b-1. -/
def rep : ℕ → ℕ → ℕ
  | _, 0 => 0
  | r, b + 1 => r / (b + 1) ^ 2 * 10 ^ b + rep (r % (b + 1) ^ 2) b

/-- A007961: n written in base where place values are positive squares. -/
def A007961 (n : ℕ) : ℕ := rep n (Nat.sqrt n)

/-- A376360 (offset 1): a(n) is the n-th number m >= 1 such that A007961(m) ends in 3. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => 1 ≤ m ∧ A007961 m % 10 = 3) (n - 1)

/-- The set of the differences a(n+1) - a(n), n >= 1, is {4, 5, 6, 7, 8, 9, 10, 11, 13}. -/
theorem main :
    {d : ℕ | ∃ n : ℕ, 1 ≤ n ∧ a (n + 1) - a n = d} = {4, 5, 6, 7, 8, 9, 10, 11, 13} := by
  sorry

end OMA.S_oeis_a376360
