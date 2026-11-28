import Mathlib

/-!
# A248366: Least positive integer m such that prime(m+n) - prime(m) divides m + n.

Source: https://oeis.org/A248366
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) exists for any n > 0. Moreover, a(n) <= n^2 except for n = 5, 10, 15, 27.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* prime(k) = `Nat.nth Nat.Prime (k - 1)`; prime(m+n) > prime(m) for n > 0.
* "a(n) <= n^2 except for n in S" is stated as: for n > 0, some m ≤ n^2 works iff n ∉ S.
* Controls (computed): a(1..12) = 1, 1, 5, 10, 175, 22, 23, 34, 35, 102, 57, 54, as in the entry;
  for n ≤ 60 a(n) exists and a(n) ≤ n^2 exactly when n ∉ {5, 10, 15, 27}.
-/

namespace OMA.S_oeis_a248366

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ prime (m + n) - prime m ∣ m + n) ∧
      ∀ n : ℕ, 0 < n → ((∃ m : ℕ, 0 < m ∧ m ≤ n ^ 2 ∧ prime (m + n) - prime m ∣ m + n) ↔
        n ∉ ({5, 10, 15, 27} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a248366
