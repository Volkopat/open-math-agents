import Mathlib

/-!
# OEIS A297445: a(n) is the least positive integer whose base-3 up-variation is n

Source: https://oeis.org/A297445 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, 2018), offset 0: a(n) = a(n-1) + 9*a(n-2) - 9*a(n-3), where a(0) = 1,
a(1) = 5, a(2) = 11. Comment: Conjecture: a(n) = least positive whose base-3 up-variation is n;
see A297441. The definition used there (A297440, A297441): suppose that a number n has base-b
digits b(m), b(m-1), ..., b(0); the base-b up-variation of n is the sum UV(n,b) of all
d(k-1) - d(k) for which d(k-1) > d(k).

Formalization notes:
* a(n) is defined by the entry's recurrence, over the integers.
* `Nat.digits 3 m` lists the base-3 digits from the least significant one, so consecutive
  entries x, y of that list are d(k-1), d(k); `upv` adds x - y when x > y (truncated subtraction
  in the natural numbers is max(0, x - y)). For example 5 = 12 in base 3 has up-variation 1 and
  11 = 102 has up-variation 2.
* `main` says, for every n, that a(n) is (the integer value of) the least element of the set of
  positive integers with base-3 up-variation n.
* Controls proved in the proof file: a(0..6) = 1, 5, 11, 47, 101, 425, 911 as in the entry.
-/

namespace OMA.S_oeis_a297445

/-- A297445(n): a(n) = a(n-1) + 9 a(n-2) - 9 a(n-3), a(0) = 1, a(1) = 5, a(2) = 11. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 5
  | 2 => 11
  | n + 3 => a (n + 2) + 9 * a (n + 1) - 9 * a n

/-- Sum of the increases between consecutive digits of a digit list written from the least
significant digit: reading from the most significant end, x after y is an increase of x - y. -/
def upv : List ℕ → ℕ
  | x :: y :: rest => (x - y) + upv (y :: rest)
  | _ => 0

/-- The base-3 up-variation of m. -/
def upVar (m : ℕ) : ℕ := upv (Nat.digits 3 m)

/-- Kimberling's conjecture: a(n) is the least positive integer whose base-3 up-variation is n. -/
theorem main : ∀ n : ℕ, ∃ m : ℕ, (m : ℤ) = a n ∧ IsLeast {k : ℕ | 0 < k ∧ upVar k = n} m := by
  sorry

end OMA.S_oeis_a297445
