import Mathlib

/-!
# A236531: a(n) = |{0 < k < n: {6*k -1 , 6*k + 1} and {prime(n-k), prime(n-k) + 2} are both twin prime pairs}|.

Source: https://oeis.org/A236531
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 2.
(ii) If n > 3 is neither 11 nor 125, then n can be written as k + m with k > 0 and m > 0 such that
6*k - 1, 6*k + 1, prime(m) + 2 and 3*prime(m) - 10 are all prime.
(iii) Any integer n > 458 can be written as p + q with q > 0 such that {p, p + 2} and
{prime(q), prime(q) + 2} are both twin prime pairs.

Formalization notes:
* prime(n) = `Nat.nth Nat.Prime (n - 1)` (prime(1) = 2). In (ii), 3*prime(m) - 10 is in ℕ; where it
  would be negative (prime(m) ≤ 3) it is 0, not prime, as negative numbers are not prime.
* Controls (computed): a(1..25) = 0, 0, 1, 2, 2, 2, 2, 3, 2, 3, 1, 4, 2, 3, 4, 1, 3, 2, 3, 5, 2, 4, 3,
  2, 4, as in the entry; (i) and (ii) hold for n < 150, (iii) for 458 < n < 700.
-/

namespace OMA.S_oeis_a236531

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A236531(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => (6 * k - 1).Prime ∧ (6 * k + 1).Prime ∧
    (prime (n - k)).Prime ∧ (prime (n - k) + 2).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 2 < n → 0 < a n) ∧
      (∀ n : ℕ, 3 < n → n ≠ 11 → n ≠ 125 → ∃ k m, 0 < k ∧ 0 < m ∧ n = k + m ∧
        (6 * k - 1).Prime ∧ (6 * k + 1).Prime ∧ (prime m + 2).Prime ∧ (3 * prime m - 10).Prime) ∧
      ∀ n : ℕ, 458 < n → ∃ p q, 0 < q ∧ n = p + q ∧ p.Prime ∧ (p + 2).Prime ∧
        (prime q).Prime ∧ (prime q + 2).Prime := by
  sorry

end OMA.S_oeis_a236531
