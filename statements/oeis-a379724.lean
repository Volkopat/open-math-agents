import Mathlib

/-!
# A379724: a(n) = A000668(n) - 1 (Mersenne primes minus 1)

Source: https://oeis.org/A379724

Conjecture (OEIS A379724 / A072868):
`A379724(n) = A072868(n) - 2`, i.e., `A072868(n) = A000668(n) + 1`, meaning that the
integers `k ≥ 2` satisfying `σ(σ(k) - k) = k` (OEIS A072868) are precisely the
numbers `p + 1` where `p` is a Mersenne prime (OEIS A000668).

Conventions:
- First terms of A000668 (Mersenne primes): `3, 7, 31, 127, 8191, ...`.
- First terms of A072868 (`σ(σ(k) - k) = k`): `4, 8, 32, 128, 8192, ...`.
- First terms of A379724: `2, 6, 30, 126, 8190, ...`.
-/

namespace OMA.S_oeis_a379724

/-- Sum of positive divisors `σ(n)` of `n : ℕ`. -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- Predicate stating that `p` is a Mersenne prime (OEIS A000668). -/
def IsMersennePrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ q : ℕ, p = 2 ^ q - 1

/-- Conjecture: an integer `k ≥ 2` satisfies `σ(σ(k) - k) = k` (OEIS A072868) if and
only if `k - 1` is a Mersenne prime (OEIS A000668). -/
theorem main :
    ∀ k : ℕ, 2 ≤ k → (sigma (sigma k - k) = k ↔ IsMersennePrime (k - 1)) := by
  sorry

end OMA.S_oeis_a379724
