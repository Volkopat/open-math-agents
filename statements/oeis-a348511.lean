import Mathlib

/-!
# OEIS A348511: squarefreeness after prime shifts

Source: https://oeis.org/A348511 (OEIS Foundation, CC BY-SA 4.0).
Credit: @kumagi

A prime shift replaces every prime factor by the next larger prime and
keeps its exponent. A348511 consists of the positive integers `k` for
which iterating that operation starting at `k` reaches `2k + 1`.
The conjecture says that every such `k` except 4 is squarefree.
-/

namespace OMA.S_oeis_a348511

/-- The least prime strictly greater than `p`. -/
noncomputable def nextPrime (p : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (p + 1))

/-- Replace the prime factors of `k` by their successors, keeping exponents. -/
noncomputable def primeShift (k : ℕ) : ℕ :=
  ∏ p ∈ k.primeFactors, (nextPrime p) ^ k.factorization p

theorem main : ∀ k : ℕ, 0 < k → k ≠ 4 →
    (∃ r : ℕ, (primeShift^[r]) k = 2 * k + 1) → Squarefree k := by
  sorry

end OMA.S_oeis_a348511
