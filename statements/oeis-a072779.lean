import Mathlib

/-!
# A072779: a(n) = sigma_2(n) + phi(n) * sigma(n).

Source: https://oeis.org/A072779
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a072779

def sigma (k n : ℕ) : ℕ :=
  n.divisors.sum fun d => d ^ k

def a (n : ℕ) : ℕ :=
  sigma 2 n + Nat.totient n * sigma 1 n

def IsProductOfTwoDistinctPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ n = p * q

theorem main :
    (∀ n : ℕ, 0 < n →
      2 * n ^ 2 ≤ a n ∧ (a n = 2 * n ^ 2 ↔ n = 1 ∨ Nat.Prime n)) ∧
    ∀ n : ℕ, 0 < n →
      (a n = 2 + 2 * n ^ 2 ↔ IsProductOfTwoDistinctPrimes n) := by
  sorry

end OMA.S_oeis_a072779
