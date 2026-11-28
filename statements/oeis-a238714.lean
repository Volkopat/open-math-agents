import Mathlib

/-!
# A238714: Final divisor of A238529(n).

Source: https://oeis.org/A238714
Credit: @agchua

Comment line of A238714, verbatim:
  Conjecture:  Every integer greater than 1, except 6, is an element of the sequence.
Offset 2; data 2, 3, 4, 5, 5, 7, 2, 3, 3, 11, 5, 13, 5, 7, 8, 17, ...

A238529(n) is the number of iterations of r -> r mod sopfr(r), started at r = n, needed to
reach 0 or 1, where sopfr(r) (A001414) is the sum of the prime factors of r counted with
multiplicity. A238714(n) is the last divisor sopfr(r) used in this process, as in the entry's
program (rem = n; while rem > 1: last = sopfr(rem); rem = rem mod last) and its examples
(a(8) = 2: 8 mod 6 = 2 and 2 mod 2 = 0; a(21) = 10: 21 mod 10 = 1).

Formalisation. finalDiv f r l runs this loop for at most f steps, with current remainder r and
last divisor l, and a n = finalDiv n n 0. Since sopfr r <= r, every step lowers the remainder,
so n steps are enough and a n = A238714(n) for every n >= 2. The conjecture is stated as:
m is a term a(n) (n >= 2) if and only if m > 1 and m is not 6.
-/

namespace OMA.S_oeis_a238714

/-- The sum of the prime factors of r counted with multiplicity (A001414). -/
def sopfr (r : ℕ) : ℕ := (Nat.primeFactorsList r).sum

/-- The loop rem := rem mod sopfr(rem) while rem > 1, with fuel f, remainder r and last divisor l;
the result is the last divisor used. -/
def finalDiv : ℕ → ℕ → ℕ → ℕ
  | 0, _, l => l
  | f + 1, r, l => if r ≤ 1 then l else finalDiv f (r % sopfr r) (sopfr r)

/-- A238714(n): the final divisor used when the loop starts at rem = n. -/
def a (n : ℕ) : ℕ := finalDiv n n 0

/-- Every integer greater than 1, except 6, is an element of the sequence, and no other
number is. -/
theorem main : ∀ m : ℕ, (∃ n : ℕ, 2 ≤ n ∧ a n = m) ↔ (2 ≤ m ∧ m ≠ 6) := by
  sorry

end OMA.S_oeis_a238714
