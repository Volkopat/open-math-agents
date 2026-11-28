import Mathlib

/-!
# A396234: Consecutive happy sexy primes whose first iterates are prime

The sequence lists the smaller term `p` of pairs of consecutive primes `p, p + 6` such that
both primes are happy (iterating the sum of the squares of the decimal digits eventually
reaches 1) and the first iteration of both primes is also prime.

Conjecture (OEIS A396234): this sequence has an infinite number of terms.

Source: https://oeis.org/A396234
Credit: @gblacher2
-/

namespace OMA.S_oeis_a396234

/-- The sum of the squares of the decimal digits of `n`. -/
def digitSqSum (n : ℕ) : ℕ := ((Nat.digits 10 n).map (· ^ 2)).sum

/-- `n` is happy: iterating `digitSqSum` eventually reaches the value 1. -/
def IsHappy (n : ℕ) : Prop := ∃ k : ℕ, digitSqSum^[k] n = 1

/-- `p` is a term: `p` and `p + 6` are consecutive primes (no prime strictly between them),
both are happy, and the first iteration of each of them is prime. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ (p + 6).Prime ∧ (∀ q : ℕ, p < q → q < p + 6 → ¬ q.Prime) ∧
    IsHappy p ∧ IsHappy (p + 6) ∧ (digitSqSum p).Prime ∧ (digitSqSum (p + 6)).Prime

/-- The sequence has infinitely many terms. -/
theorem main : Set.Infinite {p : ℕ | IsTerm p} := by
  sorry

end OMA.S_oeis_a396234
