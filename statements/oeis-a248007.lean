import Mathlib

/-!
# A248007: Least positive integer m such that m + n divides phi(m)*phi(n), where phi(.) is Euler's totient function.

Source: https://oeis.org/A248007
Credit: @azmiozgen

Conjectures (from the entry): a(n) exists for any n > 6 (Zhi-Wei Sun, Sep 29 2014). The numbers n
for which a(n) > n are 10, 12, 22, 26, 42, 78, 166, 266, 290, ...; Derek Orr conjectures that this
list is finite.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* a(n) > n means that no m with 0 < m ≤ n has the property; the second conjecture says the set of
  such n > 6 is finite.
* Controls (computed): a(7..18) = 5, 8, 3, 14, 9, 20, 11, 10, 9, 16, 7, 18, as in the entry; for
  7 ≤ n ≤ 60, a(n) exists and a(n) > n exactly at 10, 12, 22, 26, 42.
-/

namespace OMA.S_oeis_a248007



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 6 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ Nat.totient m * Nat.totient n) ∧
      {n : ℕ | 6 < n ∧ ∀ m : ℕ, 0 < m → m ≤ n → ¬ m + n ∣ Nat.totient m * Nat.totient n}.Finite := by
  sorry

end OMA.S_oeis_a248007
