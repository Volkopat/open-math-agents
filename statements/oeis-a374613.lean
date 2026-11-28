import Mathlib

namespace OMA.S_oeis_a374613

/-- Infinitely many primes satisfy the two nonprimality conditions in OEIS A374613. -/
theorem main :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ q : ℕ,
      q.Prime ∧ p < q ∧ (∀ r : ℕ, p < r → r < q → ¬ r.Prime) ∧
      ¬ (2 * (p + q) - 1).Prime ∧ ¬ (2 * (p + q) + 1).Prime} := by
  sorry

end OMA.S_oeis_a374613
