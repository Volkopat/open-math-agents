import Mathlib

/-!
# A391205: a(n) is the least k for which n^k contains at least one decimal digit 7, or -1 if there is no such k.

Source: https://oeis.org/A391205
Credit: @azmiozgen

Conjecture (from the entry): a(n) <= 15, with a(n) = -1 iff n is in A011557 and a(n) = 15 iff n/2 is
in A011557.

Formalization notes:
* A011557 is the powers of 10: 1, 10, 100, ... "n/2 is in A011557" is stated as n = 2 * 10^j.
* a(n), offset 1, takes values in ℤ: the least k with the digit 7 among the decimal digits of n^k,
  or -1 if there is none.
* The three parts are stated for every n ≥ 1.
* Controls (computed): a(1..32) = -1, 15, 3, 10, 7, 5, 1, 5, 3, -1, 6, 3, 3, 3, 3, 5, 1, 4, 5, 15, 6,
  6, 3, 2, 5, 2, 1, 2, 4, 3, 3, 3, as in the entry; for n < 3000 the maximum is 15, attained exactly at
  2, 20, 200, 2000.
-/

namespace OMA.S_oeis_a391205

/-- A391205(n): the least `k` with a digit `7` in `n^k`, or `-1` if there is none. -/
noncomputable def a (n : ℕ) : ℤ := by
  classical
  exact if h : ∃ k : ℕ, 7 ∈ Nat.digits 10 (n ^ k) then (Nat.find h : ℤ) else -1

/-- The three parts of the conjecture. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      a n ≤ 15 ∧ (a n = -1 ↔ ∃ j : ℕ, n = 10 ^ j) ∧ (a n = 15 ↔ ∃ j : ℕ, n = 2 * 10 ^ j) := by
  sorry

end OMA.S_oeis_a391205
