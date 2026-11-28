import Mathlib

/-!
# A248035: Least positive integer m such that m + n divides phi(m)^2 + phi(n)^2, where phi(.) is Euler's totient function.

Source: https://oeis.org/A248035
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) exists for any n > 0. Moreover, a(n) <= n^2 except for n = 33.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* "a(n) <= n^2 except for n = 33" is stated as: for n > 0, some m ≤ n^2 works iff n ≠ 33.
* Controls (computed): a(1..12) = 1, 3, 2, 1, 15, 14, 3, 8, 9, 30, 30, 14, as in the entry; for
  n ≤ 60 a(n) exists and a(n) ≤ n^2 exactly when n ≠ 33.
-/

namespace OMA.S_oeis_a248035



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ Nat.totient m ^ 2 + Nat.totient n ^ 2) ∧
      ∀ n : ℕ, 0 < n → ((∃ m : ℕ, 0 < m ∧ m ≤ n ^ 2 ∧ m + n ∣ Nat.totient m ^ 2 + Nat.totient n ^ 2) ↔
        n ≠ 33) := by
  sorry

end OMA.S_oeis_a248035
