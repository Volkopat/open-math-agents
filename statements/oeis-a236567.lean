import Mathlib

/-!
# A236567: a(n) = |{0 < k < n - 2: k + phi(n-k)/2 is a square}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A236567
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 5.
(ii) For n > 31, there is a positive integer k < n - 2 with phi(k) + phi(n-k)/2 a square. If n > 70
is not equal to 150, then phi(k) + phi(n-k) is a square for some 0 < k < n.
(iii) If n > 5, then phi(k) + phi(n-k)/2 is a triangular number for some 0 < k < n - 2. For each
n = 20, 21, ... there is a positive integer k < n with (phi(k) + phi(n-k))/2 a triangular number.

Formalization notes:
* phi = `Nat.totient`.
* For 0 < k < n - 2, n - k ≥ 3, so phi(n-k)/2 is exact. In the last claim (phi(k) + phi(n-k))/2
  must be an integer to be triangular, so it is stated with "phi(k) + phi(n-k) is even".
* Triangular numbers are t(t+1)/2, t ≥ 0.
* Controls (computed): a(1..25) = 0, 0, 0, 0, 0, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 4, 3, 2, 3, 1,
  3, 2, as in the entry; all claims hold for n < 150.
-/

namespace OMA.S_oeis_a236567

/-- A236567(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 (n - 2)).filter fun k => IsSquare (k + Nat.totient (n - k) / 2)).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 5 < n → 0 < a n) ∧
      (∀ n : ℕ, 31 < n → ∃ k, 0 < k ∧ k < n - 2 ∧
        IsSquare (Nat.totient k + Nat.totient (n - k) / 2)) ∧
      (∀ n : ℕ, 70 < n → n ≠ 150 → ∃ k, 0 < k ∧ k < n ∧
        IsSquare (Nat.totient k + Nat.totient (n - k))) ∧
      (∀ n : ℕ, 5 < n → ∃ k, 0 < k ∧ k < n - 2 ∧
        ∃ t : ℕ, Nat.totient k + Nat.totient (n - k) / 2 = t * (t + 1) / 2) ∧
      ∀ n : ℕ, 20 ≤ n → ∃ k, 0 < k ∧ k < n ∧ Even (Nat.totient k + Nat.totient (n - k)) ∧
        ∃ t : ℕ, (Nat.totient k + Nat.totient (n - k)) / 2 = t * (t + 1) / 2 := by
  sorry

end OMA.S_oeis_a236567
