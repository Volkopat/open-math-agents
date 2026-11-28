import Mathlib

/-!
# A286680: Smallest nonnegative m such that (1 + n)^(2^m) + n is not prime.

Source: https://oeis.org/A286680
Credit: @azmiozgen

Conjecture (from the entry): a(n) <= 6 for all n.

Formalization notes:
* a(n) ≤ 6 is stated as: some m ≤ 6 makes (1 + n)^(2^m) + n not prime (n ≥ 0, offset 0).
* Controls (computed): for n < 3000 such an m ≤ 6 exists; the entry's terms begin 0, 5, 4, 2, 0, 3.
-/

namespace OMA.S_oeis_a286680



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, ∃ m : ℕ, m ≤ 6 ∧ ¬ ((1 + n) ^ 2 ^ m + n).Prime := by
  sorry

end OMA.S_oeis_a286680
