import Mathlib

/-!
# A129786: Least k such that 2^(2^n) + k is prime

Source: https://oeis.org/A129786

Conjecture (OEIS A129786):
For every `n ≥ 5`, `a(n) ≥ 3`, where `a(n)` is the least positive integer `k` such that
`2^(2^n) + k` is prime (equivalently, every Fermat number `F_n = 2^(2^n) + 1` is composite
for `n ≥ 5`).

Conventions:
- Offset: `0`; first terms: `a(0) = 1`, `a(1) = 1`, `a(2) = 1`, `a(3) = 1`, `a(4) = 1`,
  `a(5) = 15`, `a(6) = 13`, `a(7) = 51`, ...
- Minimality is expressed via a predicate `IsLeastValid` to avoid `Nat.find`.
-/

namespace OMA.S_oeis_a129786

/-- Predicate stating that `k ≥ 1` and `2^(2^n) + k` is prime. -/
def IsValid (n k : ℕ) : Prop :=
  1 ≤ k ∧ Nat.Prime (2 ^ (2 ^ n) + k)

/-- Predicate stating that `k = a(n)` is the least positive integer with `2^(2^n) + k` prime
(OEIS A129786). -/
def IsLeastValid (n k : ℕ) : Prop :=
  IsValid n k ∧ ∀ j : ℕ, IsValid n j → k ≤ j

/-- Conjecture: `a(n) ≥ 3` for every `n ≥ 5`. -/
theorem main :
    ∀ n k : ℕ, 5 ≤ n → IsLeastValid n k → 3 ≤ k := by
  sorry

end OMA.S_oeis_a129786
