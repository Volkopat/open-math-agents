import Mathlib

/-!
# A248004: Least positive integer m with prime(m*n) == 1 (mod m+n).

Source: https://oeis.org/A248004
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) exists for any n > 0. Moreover, a(n) does not exceed n*(n-1)/2 if n > 2.
(ii) For each positive integer n, there is an integer m > 0 with prime(m*n) == -1 (mod m+n).
Moreover, we may require that m does not exceed n*(n-1)/2 if n > 2.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* prime(k) = `Nat.nth Nat.Prime (k - 1)`. "x == -1 (mod d)" is d | x + 1.
* Controls (computed): a(1..12) = 3, 4, 1, 2, 2, 15, 1, 1, 5, 10, 2, 3, as in the entry; both parts
  hold for n ≤ 60.
-/

namespace OMA.S_oeis_a248004

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ prime (m * n) ≡ 1 [MOD m + n]) ∧
      (∀ n : ℕ, 2 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) / 2 ∧ prime (m * n) ≡ 1 [MOD m + n]) ∧
      (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ prime (m * n) + 1) ∧
      ∀ n : ℕ, 2 < n → ∃ m : ℕ, 0 < m ∧ m ≤ n * (n - 1) / 2 ∧ m + n ∣ prime (m * n) + 1 := by
  sorry

end OMA.S_oeis_a248004
