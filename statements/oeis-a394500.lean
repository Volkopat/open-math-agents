import Mathlib

/-!
# A394500: Ways to represent n = k + p where p is prime and k > 0 is not squarefree.

Source: https://oeis.org/A394500
Credit: @azmiozgen

Conjecture (from the entry): a(n) > 0 for n > 24.

Formalization notes:
* a(n) > 0 is the existence of a prime p and a non-squarefree k > 0 with n = k + p.
* Controls (computed): every n with 24 < n < 20000 is represented; the entry's terms begin
  0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 3.
-/

namespace OMA.S_oeis_a394500



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 24 < n → ∃ k p : ℕ, 0 < k ∧ ¬ Squarefree k ∧ p.Prime ∧ k + p = n := by
  sorry

end OMA.S_oeis_a394500
