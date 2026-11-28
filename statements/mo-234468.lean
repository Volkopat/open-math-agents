import Mathlib.Algebra.Polynomial.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Field.Rat

/-! Source: https://mathoverflow.net/questions/234468 -/

open scoped BigOperators
open Polynomial

namespace OMA.S_mo_234468

noncomputable def divisorPolynomial (n : ℕ) : ℚ[X] :=
  ∑ d ∈ n.divisors, X ^ d

def admissible (i n : ℕ) : Prop :=
  0 < n ∧ (X ^ (2 ^ i) + 1 : ℚ[X]) ∣ divisorPolynomial n

/-- Prime powers whose exponent cycles pair the two halves of the residue classes,
and pairs from the two exceptional prime classes. -/
def candidate (i n : ℕ) : Prop :=
  (∃ p d : ℕ, p.Prime ∧ 0 < d ∧
    (p ^ d) % (2 ^ (i + 1)) = 1 + 2 ^ i ∧ n = p ^ (2 * d - 1)) ∨
  (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % (2 ^ (i + 1)) = 2 ^ (i + 1) - 1 ∧
    q % (2 ^ (i + 1)) = 2 ^ i - 1 ∧ n = p * q)

/-- The smallest index whose divisor polynomial is divisible by X^(2^i)+1. -/
theorem main :
    IsLeast {n : ℕ | admissible 0 n} 2 ∧
    IsLeast {n : ℕ | admissible 1 n} 3 ∧
    ∀ i : ℕ, 2 ≤ i →
      (∃ n : ℕ, IsLeast {m : ℕ | candidate i m} n) ∧
      (∀ n : ℕ, IsLeast {m : ℕ | admissible i m} n ↔ IsLeast {m : ℕ | candidate i m} n) := by
  sorry

end OMA.S_mo_234468
