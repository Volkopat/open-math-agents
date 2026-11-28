import Mathlib

/-!
# A308818: a(n) = a(a(n-1) mod n) + a(a(n-2) mod n) with a(0)=2 and a(1)=3.

Source: https://oeis.org/A308818
Credit: @rpabani

Conjecture (ii) in OEIS A308818: there is an integer greater than 1 that can never appear in this
sequence.

The recurrence determines the sequence uniquely, because both indices a(n-1) mod n and
a(n-2) mod n are smaller than n. The statement is therefore made about any sequence of natural
numbers with these initial values and this recurrence. All terms are positive integers, so the
integer greater than 1 is taken to be a natural number. Conjecture (i) of the source, that the
sequence does not enter a cycle, is a separate statement and is not included.
-/

namespace OMA.S_oeis_a308818

theorem main : ∀ a : ℕ → ℕ, a 0 = 2 → a 1 = 3 →
    (∀ n : ℕ, 2 ≤ n → a n = a (a (n - 1) % n) + a (a (n - 2) % n)) →
    ∃ m : ℕ, 1 < m ∧ ∀ n : ℕ, a n ≠ m := by
  sorry

end OMA.S_oeis_a308818
