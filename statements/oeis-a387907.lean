import Mathlib

/-!
# A387907: a(n) = position of first odd digit of 2^n, starting from left, or 0 if no odd digit exists.

Source: https://oeis.org/A387907
Credit: @azmiozgen

Conjecture (from the entry; the "2048 problem"): a(n) is positive for n >= 12.

Formalization notes:
* a(n) is positive exactly when 2^n has an odd decimal digit, so the conjecture is stated as:
  for every n ≥ 12, some decimal digit of 2^n is odd.
* Controls (computed): for n < 200 the powers 2^n with no odd digit are n = 1, 2, 3, 6, 11
  (2, 4, 8, 64, 2048), matching the zeros of the entry.
-/

namespace OMA.S_oeis_a387907

/-- For `n ≥ 12`, `2^n` has an odd decimal digit. -/
theorem main : ∀ n : ℕ, 12 ≤ n → ∃ d ∈ Nat.digits 10 (2 ^ n), Odd d := by
  sorry

end OMA.S_oeis_a387907
