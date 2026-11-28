import Mathlib

/-!
# A248590: Least positive integer m such that prime(m) == 1 (mod m + n).

Source: https://oeis.org/A248590
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) exists for any n > 0. Moreover, a(n) < n*(n-1) if n > 3.
(ii) For any n > 0, there is a positive integer m such that prime(m) == -1 (mod m + n). Moreover,
we may require m < n*(n-1) if n > 1.

Formalization notes:
* a(n) is the least positive m with the property, so "a(n) exists" is the existence of such an m,
  and "a(n) ≤ B" is the existence of such an m with m ≤ B.
* prime(k) = `Nat.nth Nat.Prime (k - 1)`. "x == -1 (mod d)" is d | x + 1.
* Controls (computed): a(1..12) = 3, 4, 19, 10, 5, 6, 13, 15, 7, 8, 31, 17, as in the entry; both parts
  hold for n ≤ 60.
-/

namespace OMA.S_oeis_a248590

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ prime m ≡ 1 [MOD m + n]) ∧
      (∀ n : ℕ, 3 < n → ∃ m : ℕ, 0 < m ∧ m < n * (n - 1) ∧ prime m ≡ 1 [MOD m + n]) ∧
      (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ m + n ∣ prime m + 1) ∧
      ∀ n : ℕ, 1 < n → ∃ m : ℕ, 0 < m ∧ m < n * (n - 1) ∧ m + n ∣ prime m + 1 := by
  sorry

end OMA.S_oeis_a248590
