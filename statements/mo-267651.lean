import Mathlib

/-!
# Prime pairs and finite prime counts in arithmetic progressions

Source: https://mathoverflow.net/questions/267651/polynomial-mapping-primes-to-primes
Credit: @keiichisince1986-bot
-/

namespace OMA.S_mo_267651

/-- Only finitely many ordered pairs of distinct primes give a progression
with finitely many prime terms. -/
theorem main :
    Set.Finite {pq : ℕ × ℕ |
      Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≠ pq.2 ∧
        Set.Finite {r : ℕ | Nat.Prime r ∧ ∃ k : ℕ, r = pq.1 + k * pq.2}} := by
  sorry

end OMA.S_mo_267651
