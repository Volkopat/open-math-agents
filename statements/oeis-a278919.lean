import Mathlib

/-!
# A278919: Numbers k such that phi(k - 2) divides sigma(k - 1) + 1

Source: https://oeis.org/A278919

Conjecture (OEIS A278919):
There are only finitely many integers `k ≥ 3` such that `φ(k - 2)` divides `σ(k - 1) + 1`.

Conventions:
- Offset: `1`; first terms: `3, 4, 5, 17, 26, 257, ...`.
- We require `3 ≤ k` so that `k - 2 ≥ 1` and `k - 1 ≥ 2`.
-/

namespace OMA.S_oeis_a278919

/-- Sum of positive divisors `σ(n)` of `n : ℕ`. -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- The set of integers `k ≥ 3` such that `φ(k - 2) ∣ σ(k - 1) + 1` (OEIS A278919). -/
def S : Set ℕ :=
  {k : ℕ | 3 ≤ k ∧ Nat.totient (k - 2) ∣ sigma (k - 1) + 1}

/-- Conjecture: the set of terms of OEIS A278919 is finite. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a278919
