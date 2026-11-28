import Mathlib

/-!
# A240562: Integers whose squares are in A000073 (tribonacci numbers)

Source: https://oeis.org/A240562

Conjecture (OEIS A240562):
There are only finitely many nonnegative integers `k` such that `k^2` is a tribonacci
number (OEIS A000073).

Conventions:
- Offset: `1`; known terms: `0` (`0^2 = T(0)`), `1` (`1^2 = T(2)`),
  `2` (`2^2 = T(5) = 4`), `9` (`9^2 = T(10) = 81`).
- Tribonacci numbers A000073: `T(0) = 0`, `T(1) = 0`, `T(2) = 1`,
  `T(n + 3) = T(n) + T(n + 1) + T(n + 2)`.
-/

namespace OMA.S_oeis_a240562

/-- Tribonacci numbers (OEIS A000073): `0, 0, 1, 1, 2, 4, 7, 13, 24, 44, 81, ...`. -/
def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci n + tribonacci (n + 1) + tribonacci (n + 2)

/-- The set of natural numbers `k` whose square is a tribonacci number (OEIS A240562). -/
def S : Set ℕ :=
  {k : ℕ | ∃ n : ℕ, k ^ 2 = tribonacci n}

/-- Conjecture: there are only finitely many squares among the tribonacci numbers. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a240562
