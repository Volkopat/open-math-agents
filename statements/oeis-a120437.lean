import Mathlib

/-!
# A120437: the recursion for the differences of A037314

Source: https://oeis.org/A120437
Credit: @ivillar

Status: known result: the entry records that the recursion is correct (Franklin T. Adams-Watters, Jul 24 2006).

A037314 (offset 0) lists the numbers whose base-3 and base-9 expansions have the same digit sum:
A037314(n) = Sum d(i)*9^i, where Sum d(i)*3^i is the base-3 representation of n (write n in base 3
and read it in base 9); data 0, 1, 2, 9, 10, 11, 18, 19, 20, 81, ...
A120437 (offset 1) is its sequence of differences, a(n) = A037314(n) - A037314(n-1);
data 1, 1, 7, 1, 1, 7, 1, 1, 61, 1, 1, 7, ...

Conjecture (in the formula section of A120437): the sequence is given by the recursion
a(n) = 1 if n = 1, a(n) = 9*a(3^(k-1)) - 2 if n = 3^k for some k > 0, and
a(n) = a(n - 3^(k-1)) if 3^(k-1) < n < 3^k for some k > 0.
Franklin T. Adams-Watters (Jul 24 2006) records in the entry that the recursion is correct.

Formalization: `b n` is A037314(n), computed from the base-3 digits of n (least significant
first) read in base 9. `a n` is the difference as an integer. The three clauses of the recursion
are stated as a conjunction.
-/

namespace OMA.S_oeis_a120437

/-- A037314(n): write n in base 3 and read the digits in base 9. -/
def b (n : ℕ) : ℕ := Nat.ofDigits 9 (Nat.digits 3 n)

/-- A120437(n) = A037314(n) - A037314(n-1), for n ≥ 1. -/
def a (n : ℕ) : ℤ := (b n : ℤ) - (b (n - 1) : ℤ)

/-- The conjectured recursion for A120437. -/
theorem main :
    a 1 = 1 ∧
    (∀ k : ℕ, 0 < k → a (3 ^ k) = 9 * a (3 ^ (k - 1)) - 2) ∧
    (∀ k n : ℕ, 0 < k → 3 ^ (k - 1) < n → n < 3 ^ k → a n = a (n - 3 ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a120437
