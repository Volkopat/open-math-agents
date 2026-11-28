import Mathlib

/-!
# A382054: a(n) = least positive integer m such that when m*(m+1) is written in base n, it does not contain the digit n-1 and contains every single digit from 0 to n-2 exactly once, or 0 if no such number exists.

Source: https://oeis.org/A382054
Credit: @azmiozgen

Conjecture (from the entry): a(n) > 0 if n > 4 and n <> 3 (mod 4).

Formalization notes:
* "m(m+1) written in base n contains each digit 0..n-2 exactly once and no digit n-1" means its list of
  base-n digits (`Nat.digits n`) is a permutation of [0, 1, ..., n-2]. a(n) > 0 is the existence of
  such m ≥ 1.
* Controls (computed): a(3..11) = 0, 0, 14, 54, 0, 616, 2251, 12069, 0, as in the entry.
-/

namespace OMA.S_oeis_a382054



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 4 < n → n % 4 ≠ 3 →
      ∃ m : ℕ, 0 < m ∧ (Nat.digits n (m * (m + 1))).Perm (List.range (n - 1)) := by
  sorry

end OMA.S_oeis_a382054
