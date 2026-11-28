import Mathlib

/-!
# A248197: Least positive integer m such that m + n divides prime(prime(m)) + prime(prime(n)).

Source: https://oeis.org/A248197
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) exists for any n > 0. Moreover, a(n) < n*(n-1) if n > 2.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* prime(k) = `Nat.nth Nat.Prime (k - 1)`.
* Controls (computed): a(1..12) = 1, 9, 4, 1, 17, 12, 3, 4, 2, 4, 15, 6, as in the entry; both parts
  hold for n ≤ 60.
-/

namespace OMA.S_oeis_a248197

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ prime (prime m) + prime (prime n)) ∧
      ∀ n : ℕ, 2 < n → ∃ m : ℕ, 0 < m ∧ m < n * (n - 1) ∧ m + n ∣ prime (prime m) + prime (prime n) := by
  sorry

end OMA.S_oeis_a248197
