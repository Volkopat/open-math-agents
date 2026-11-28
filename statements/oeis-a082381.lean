import Mathlib

/-!
# A082381: Sequence of the squared digital root of a number until 1 or 4 is reached. The initial numbers 1,2,..n are not output.

Source: https://oeis.org/A082381
Credit: @agchua

Comment of A082381 (unsigned; the entry is by Cino Hilliard, Apr 13 2003):
  Conjecture: The sequence always terminates with 1 or the 4 16 37 58 89 145 42 20 4... loop
  (cf. A080709).
As M. F. Hasler explains in the entry (Dec 18 2009), row n of the sequence lists the successive
values of the map sum of the squares of the decimal digits (f below), starting with n >= 1, until
1 or 4 is reached; a row ends at the first k >= 1 with f^[k] n = 1 or f^[k] n = 4. So the
conjecture says: every row is finite, and the loop through 4 is 4, 16, 37, 58, 89, 145, 42, 20, 4.
The rows start at n = 1 (offset 1); n = 0 is not a row (f 0 = 0).
-/

namespace OMA.S_oeis_a082381

/-- The squared digital root map: the sum of the squares of the decimal digits of n. -/
def f (n : ℕ) : ℕ := ((Nat.digits 10 n).map (fun d => d ^ 2)).sum

/-- The comment's conjecture: f maps 4 to 16 to 37 to 58 to 89 to 145 to 42 to 20 to 4 (the
loop), and for every n >= 1 some iterate f^[k] n with k >= 1 equals 1 or 4. -/
theorem main : (f 4 = 16 ∧ f 16 = 37 ∧ f 37 = 58 ∧ f 58 = 89 ∧ f 89 = 145 ∧ f 145 = 42 ∧
    f 42 = 20 ∧ f 20 = 4) ∧
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ (f^[k] n = 1 ∨ f^[k] n = 4) := by
  sorry

end OMA.S_oeis_a082381
