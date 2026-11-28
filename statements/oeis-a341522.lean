import Mathlib

namespace OMA.S_oeis_a341522

theorem main :
    ∀ (primeShift doudna invDoudna : ℕ → ℕ),
      primeShift 1 = 1 →
      (∀ x : ℕ, primeShift (2 * x) = 3 * primeShift x) →
      doudna 1 = 1 →
      (∀ k : ℕ, 1 ≤ k → doudna (2 * k) = 2 * doudna k) →
      (∀ k : ℕ, doudna (2 * k + 1) = primeShift (doudna (k + 1))) →
      (∀ m : ℕ, 1 ≤ m → invDoudna (doudna m) = m - 1) →
      ∀ n : ℕ,
        invDoudna (3 * doudna (n + 1)) = 1 + 2 * n + 2 ^ padicValNat 2 (n + 1) := by
  sorry

end OMA.S_oeis_a341522
