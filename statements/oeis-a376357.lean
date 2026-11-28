import Mathlib

/-!
# A376357: Positions of numbers in A007961 that end in 0.

Source: https://oeis.org/A376357
Credit: @agchua

Comment line of A376357 (Clark Kimberling, Sep 25 2024), verbatim:
  Conjecture: {a(n+1) - a(n) : n >= 1} = {1,2,3,4}. (See related conjectures at A376358-A376360.)
Offset of A376357: 1 (data 4, 8, 9, 13, 16, 20, 24, 25, ...).

A007961 (offset 1) is n written in base where place values are positive squares. As in the
entry's Maple program (R. J. Mathar), with k = floor(sqrt(n)) the digits are computed greedily
for the place values k^2, (k-1)^2, ..., 1^2: the digit of b^2 is floor(r/b^2) for the current
remainder r, the remainder then becomes r mod b^2, and the digit of b^2 is written at the decimal
position b-1 (units for b = 1). So A007961(n) = rep(n, floor(sqrt(n))) with rep as below; for
example A007961(8) = 20 and A007961(34) = 10100.
A376357 lists the n >= 1 such that A007961(n) ends in 0 (A007961(n) mod 10 = 0) in increasing
order, so a(n) is Nat.nth of that predicate at n - 1 (Nat.nth counts from 0). The conjecture says
that the set of the differences a(n+1) - a(n), n >= 1, is exactly {1, 2, 3, 4}.
-/

namespace OMA.S_oeis_a376357

/-- rep r b: r written greedily with the place values b^2, (b-1)^2, ..., 1^2, read as a decimal
number; the digit of b^2 stands at the decimal position b-1. -/
def rep : ℕ → ℕ → ℕ
  | _, 0 => 0
  | r, b + 1 => r / (b + 1) ^ 2 * 10 ^ b + rep (r % (b + 1) ^ 2) b

/-- A007961: n written in base where place values are positive squares. -/
def A007961 (n : ℕ) : ℕ := rep n (Nat.sqrt n)

/-- A376357 (offset 1): a(n) is the n-th number m >= 1 such that A007961(m) ends in 0. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => 1 ≤ m ∧ A007961 m % 10 = 0) (n - 1)

/-- The set of the differences a(n+1) - a(n), n >= 1, is {1, 2, 3, 4}. -/
theorem main : {d : ℕ | ∃ n : ℕ, 1 ≤ n ∧ a (n + 1) - a n = d} = {1, 2, 3, 4} := by
  sorry

end OMA.S_oeis_a376357