import Mathlib

/-!
# A298943: Lower of two consecutive Mersenne prime exponents with record first difference

Source: https://oeis.org/A298943

Conjecture (OEIS A298943):
The sequence of Mersenne prime exponents `p` (where `2^p - 1` is prime) whose gap to
the next Mersenne prime exponent `q` sets a new strict record is infinite.

Conventions:
- Offset: `1`; first terms: `2, 3, 7, 19, 31, 127, 607, 1279, 2281, 3217, 4423, ...`.
- The first consecutive pairs of Mersenne prime exponents `(2, 3)`, `(3, 5)`, `(7, 13)`,
  `(19, 31)`, `(31, 61)`, `(127, 521)` have record gaps `1, 2, 6, 12, 30, 394`.
-/

namespace OMA.S_oeis_a298943

/-- Predicate stating that `p` is a Mersenne prime exponent (OEIS A000043). -/
def IsMersenneExp (p : ℕ) : Prop :=
  Nat.Prime (2 ^ p - 1)

/-- Predicate stating that `(p, q)` are consecutive Mersenne prime exponents. -/
def IsConsecMersenneExp (p q : ℕ) : Prop :=
  IsMersenneExp p ∧ IsMersenneExp q ∧ p < q ∧
    ∀ r : ℕ, p < r → r < q → ¬ IsMersenneExp r

/-- The set of lower Mersenne prime exponents attaining a strict record gap to the next
Mersenne prime exponent (OEIS A298943). -/
def S : Set ℕ :=
  {p : ℕ | ∃ q : ℕ, IsConsecMersenneExp p q ∧
    ∀ p' q' : ℕ, p' < p → IsConsecMersenneExp p' q' → q' - p' < q - p}

/-- Conjecture: the sequence A298943 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a298943
