import Mathlib

/-!
# A248369: Least positive integer m such that prime(m+n) - prime(m) divides m.

Source: https://oeis.org/A248369
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) exists for any n > 0. Moreover, for n > 9 we have a(n) < n^2 except for n = 12, 19, 36, 38.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* prime(k) = `Nat.nth Nat.Prime (k - 1)`.
* "a(n) < n^2 except for n in S" is stated as: for n > 9, some m < n^2 works iff n ∉ S.
* Controls (computed): a(1..12) = 1, 6, 54, 18, 26, 24, 80, 120, 180, 48, 70, 160, as in the entry;
  for 9 < n ≤ 60 a(n) < n^2 exactly when n ∉ {12, 19, 36, 38}.
-/

namespace OMA.S_oeis_a248369

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ prime (m + n) - prime m ∣ m) ∧
      ∀ n : ℕ, 9 < n → ((∃ m : ℕ, 0 < m ∧ m < n ^ 2 ∧ prime (m + n) - prime m ∣ m) ↔
        n ∉ ({12, 19, 36, 38} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a248369
