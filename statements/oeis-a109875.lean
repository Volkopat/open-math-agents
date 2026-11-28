import Mathlib

/-!
# A109875: Chen primes p such that p + 2 is a golden semiprime

Source: https://oeis.org/A109875

Conjecture (OEIS A109875):
There are infinitely many primes `p` such that `p + 2` is a golden semiprime
(OEIS A108540), i.e., `p + 2 = q * r` for primes `q, r` satisfying `|q * φ - r| < 1`,
where `φ = (1 + √5) / 2` is the golden ratio.

Conventions:
- Offset: `1`; first terms: `13, 587, 1361, 15227, ...`.
- For `p = 13`, `p + 2 = 15 = 3 * 5` with `|3 * φ - 5| ≈ 0.146 < 1`.
-/

namespace OMA.S_oeis_a109875

/-- Predicate stating that `m` is a golden semiprime (OEIS A108540): `m = q * r` with
`q, r` prime and `|q * φ - r| < 1`. -/
def IsGoldenSemiprime (m : ℕ) : Prop :=
  ∃ q r : ℕ, Nat.Prime q ∧ Nat.Prime r ∧ m = q * r ∧
    |(q : ℝ) * ((1 + Real.sqrt 5) / 2) - (r : ℝ)| < 1

/-- The set of primes `p` such that `p + 2` is a golden semiprime (OEIS A109875). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ IsGoldenSemiprime (p + 2)}

/-- Conjecture: the sequence A109875 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a109875
