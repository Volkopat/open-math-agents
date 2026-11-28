import Mathlib

/-!
# A232502: Number of ways to write n = k + m (0 < k < m) with 2*prime(m) - prime(k) prime.

Source: https://oeis.org/A232502
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 4, and a(n) = 1 only for n = 5, 6, 7, 9, 11, 14, 17, 21, 34, 43.
(ii) Any integer n > 4 can be written as k + m (0 < k < m) with 2*prime(m) + prime(k) prime.

Formalization notes:
* prime(m) = `Nat.nth Nat.Prime (m - 1)` (prime(1) = 2); m = n - k and k < m is 2k < n.
  2*prime(m) - prime(k) > 0 for k < m.
* "a(n) = 1 only for n in S" is stated as: for n ≥ 1, a(n) = 1 iff n ∈ S.
* Controls (computed): for n < 400, a(n) > 0 for n > 4, a(n) = 1 exactly on the listed set, and
  (ii) holds.
-/

namespace OMA.S_oeis_a232502

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A232502(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => 2 * k < n ∧ (2 * prime (n - k) - prime k).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 4 < n → 0 < a n) ∧
      (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ({5, 6, 7, 9, 11, 14, 17, 21, 34, 43} : Finset ℕ))) ∧
      ∀ n : ℕ, 4 < n → ∃ k, 0 < k ∧ 2 * k < n ∧ (2 * prime (n - k) + prime k).Prime := by
  sorry

end OMA.S_oeis_a232502
