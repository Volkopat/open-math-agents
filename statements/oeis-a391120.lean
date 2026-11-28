import Mathlib

/-!
# A391120: a(n) is the least k for which n^k contains at least one decimal digit 9, or -1 if there is no such k.

Source: https://oeis.org/A391120
Credit: @azmiozgen

Conjecture (from the entry): a(n) <= 12, with a(n) = -1 iff n is in A011557 and a(n) = 12 iff
n/2 is in A011557.

Formalization notes:
* A011557 is the powers of 10: 1, 10, 100, ... "n/2 is in A011557" is stated as n = 2 * 10^j.
* a(n), offset 1, takes values in ℤ: the least k with the digit 9 among the decimal digits of
  n^k, or -1 if there is none.
* The three parts are stated for every n ≥ 1.
* Controls (computed): a(1..32) = -1, 12, 2, 6, 8, 4, 2, 4, 1, -1, 7, 6, 2, 2, 5, 3, 2, 4, 1,
  12, 3, 6, 2, 5, 4, 4, 2, 3, 1, 2, 2, 7, as in the entry.
-/

namespace OMA.S_oeis_a391120

/-- A391120(n): the least `k` with a digit `9` in `n^k`, or `-1` if there is none. -/
noncomputable def a (n : ℕ) : ℤ := by
  classical
  exact if h : ∃ k : ℕ, 9 ∈ Nat.digits 10 (n ^ k) then (Nat.find h : ℤ) else -1

/-- The three parts of the conjecture. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      a n ≤ 12 ∧ (a n = -1 ↔ ∃ j : ℕ, n = 10 ^ j) ∧ (a n = 12 ↔ ∃ j : ℕ, n = 2 * 10 ^ j) := by
  sorry

end OMA.S_oeis_a391120
