import Mathlib

/-!
# A242171: Least prime divisor of B(n) which does not divide any B(k) with k < n, or 1 if such a primitive prime divisor of B(n) does not exist, where B(n) is the n-th Bell number given by A000110.

Source: https://oeis.org/A242171
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
(i) a(n) > 1 for all n > 1.
(ii) For any integer n > 2, the derangement number D(n) given by A000166 has a prime divisor
dividing none of those D(k) with 1 < k < n.

Formalization notes:
* Bell numbers are defined by B(0) = 1 and B(n+1) = Sum_{k=0..n} binomial(n,k) B(k); derangement
  numbers are Mathlib's `numDerangements`.
* a(n) > 1 means B(n) has a prime divisor dividing no B(k) with k < n.
* Controls (computed): B(0..7) = 1, 1, 2, 5, 15, 52, 203, 877; both parts hold for n < 120.
-/

namespace OMA.S_oeis_a242171

/-- The Bell numbers A000110. -/
def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), n.choose k * bell k

/-- Both parts of the conjecture. -/
theorem main :
    (∀ n : ℕ, 1 < n → ∃ p : ℕ, p.Prime ∧ p ∣ bell n ∧ ∀ k : ℕ, k < n → ¬ p ∣ bell k) ∧
      ∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ p ∣ numDerangements n ∧
        ∀ k : ℕ, 1 < k → k < n → ¬ p ∣ numDerangements k := by
  sorry

end OMA.S_oeis_a242171
