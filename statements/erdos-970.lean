import Mathlib

/-!
# Erdős Problem 970

Source: https://www.erdosproblems.com/970
Credit: @mattdorman

The source asks: let `h(k)` be Jacobsthal's function, the minimal `m` such that, if `n` has at most
`k` prime factors, then any set of `m` consecutive integers contains an integer coprime to `n`.
Is it true that `h(k) ≪ k²`?

Reading used here: `n` ranges over positive integers and "at most `k` prime factors" counts
distinct primes (`n.primeFactors.card ≤ k`), the standard reading for Jacobsthal's function.
`h(k) ≪ k²` means there is a constant `C` with `h(k) ≤ C k²` for all `k ≥ 1`; since `h(k)` is
minimal, this says every run of consecutive integers `x ≤ y < x + C k²` contains one coprime to
`n`, and the statement is written in that form. The statement below is the affirmative answer
(Jacobsthal's conjecture).
-/

namespace OMA.S_erdos_970

theorem main :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
      ∀ x : ℤ, ∃ y : ℤ, x ≤ y ∧ (y : ℝ) < x + C * (k : ℝ) ^ 2 ∧ Int.gcd y n = 1 := by
  sorry

end OMA.S_erdos_970
