import Mathlib

/-!
# OEIS A297443: a(n) is the least positive integer whose base-3 total variation is n

Source: https://oeis.org/A297443 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, 2018), offset 0: a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3) + 3*a(n-4) -
3*a(n-5), where a(0) = 1, a(1) = 3, a(2) = 6, a(3) = 11, a(4) = 20, a(5) = 33. Comment:
Conjecture: a(n) = least positive whose base-3 total variation is n; see A297440. A297440: for a
number with base-b digits b(m), ..., b(0), the down-variation is the sum of all d(i) - d(i-1)
with d(i) > d(i-1), the up-variation the sum of all d(k-1) - d(k) with d(k-1) > d(k), and the
total variation is their sum, that is the sum of the absolute differences of consecutive digits.

Formalization notes:
* a(n) is defined by the entry's recurrence with its six initial values, over the integers.
* `Nat.digits 3 m` lists the base-3 digits from the least significant one; `tvar` adds
  |x - y| (written (x - y) + (y - x) in the natural numbers) over consecutive entries.
  For example 11 = 102 in base 3 has total variation 1 + 2 = 3.
* `main` says, for every n, that a(n) is (the integer value of) the least element of the set of
  positive integers with base-3 total variation n.
* Controls proved in the proof file: a(0..9) = 1, 3, 6, 11, 20, 33, 60, 101, 182, 303 as in the
  entry.
-/

namespace OMA.S_oeis_a297443

/-- A297443(n): a(n) = a(n-1) + 2a(n-2) - 2a(n-3) + 3a(n-4) - 3a(n-5), a(0..5) =
1, 3, 6, 11, 20, 33. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 11
  | 4 => 20
  | 5 => 33
  | n + 6 => a (n + 5) + 2 * a (n + 4) - 2 * a (n + 3) + 3 * a (n + 2) - 3 * a (n + 1)

/-- Sum of the absolute differences of consecutive entries of a digit list
((x - y) + (y - x) is |x - y| for natural numbers). -/
def tvar : List ℕ → ℕ
  | x :: y :: rest => ((x - y) + (y - x)) + tvar (y :: rest)
  | _ => 0

/-- The base-3 total variation of m. -/
def totVar (m : ℕ) : ℕ := tvar (Nat.digits 3 m)

/-- Kimberling's conjecture: a(n) is the least positive integer whose base-3 total variation is
n. -/
theorem main : ∀ n : ℕ, ∃ m : ℕ, (m : ℤ) = a n ∧ IsLeast {k : ℕ | 0 < k ∧ totVar k = n} m := by
  sorry

end OMA.S_oeis_a297443
