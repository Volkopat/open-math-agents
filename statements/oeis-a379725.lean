import Mathlib

/-!
# A379725: a(n) = A023900(n * A000396(n))

Source: https://oeis.org/A379725

Conjecture (OEIS A379725):
For every `n ≥ 1`, letting `P` be the `n`-th perfect number (`A000396(n)`), we have
`A023900(n * P) = (-1)^(n + 1) * A023900(n) * A023900(P)`, where
`A023900(m) = ∏_{p ∣ m} (1 - p)` is the Dirichlet inverse of Euler's totient function.

Conventions:
- Offset: `1`; first perfect numbers (A000396): `6, 28, 496, 8128, ...`.
- First terms of A379725: `a(1) = 2`, `a(2) = 6`, `a(3) = -60`, `a(4) = 126`, ...
- Using `Set.ncard {m : ℕ | IsPerfect m ∧ m ≤ P} = n` characterizes `P = A000396(n)`
  without assuming that infinitely many perfect numbers exist.
-/

namespace OMA.S_oeis_a379725

/-- Dirichlet inverse of Euler's totient function `∏_{p ∣ m} (1 - p)` (OEIS A023900). -/
def a023900 (m : ℕ) : ℤ :=
  ∏ p ∈ m.primeFactors, (1 - (p : ℤ))

/-- Predicate stating that `m` is a perfect number (OEIS A000396). -/
def IsPerfect (m : ℕ) : Prop :=
  1 ≤ m ∧ ∑ d ∈ m.divisors, d = 2 * m

/-- Conjecture: if `P` is the `n`-th perfect number (`n ≥ 1`), then
`A023900(n * P) = (-1)^(n + 1) * A023900(n) * A023900(P)`. -/
theorem main :
    ∀ n P : ℕ, 1 ≤ n → IsPerfect P → Set.ncard {m : ℕ | IsPerfect m ∧ m ≤ P} = n →
      a023900 (n * P) = (-1 : ℤ) ^ (n + 1) * a023900 n * a023900 P := by
  sorry

end OMA.S_oeis_a379725
