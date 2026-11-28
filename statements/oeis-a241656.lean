import Mathlib

/-!
# A241656: every even number greater than 22 is a sum of two semiprimes

Source: https://oeis.org/A241656
Credit: @coleman415

The entry records: *Conjecture: every even number greater than 22 is a sum of two semiprimes.
Only 2, 4, 6 & 22 cannot be so represented.*

Conventions:
- A semiprime is a product of exactly two primes, not necessarily distinct (OEIS A001358:
  4, 6, 9, 10, 14, 15, ...).
- The two semiprimes of a representation may be equal (the entry's own data has
  `a(4) = 4`, that is `8 = 4 + 4`).
- The second sentence is about positive even numbers, the range `2n`, `n ≥ 1` of the sequence.

`main` is the conjunction of the two sentences: (1) the conjecture itself, and (2) the list of
exceptions, that is, a positive even number is a sum of two semiprimes exactly when it is not
2, 4, 6 or 22.
-/

namespace OMA.S_oeis_a241656

/-- `n` is a semiprime: a product of two primes, not necessarily distinct (OEIS A001358). -/
def IsSemiprime (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q

/-- `n` is a sum of two semiprimes (possibly equal). -/
def IsSumOfTwoSemiprimes (n : ℕ) : Prop :=
  ∃ a b : ℕ, IsSemiprime a ∧ IsSemiprime b ∧ n = a + b

/-- The conjecture of OEIS A241656, with its list of exceptions. -/
theorem main :
    (∀ n : ℕ, Even n → 22 < n → IsSumOfTwoSemiprimes n) ∧
    (∀ n : ℕ, Even n → 0 < n →
      (¬ IsSumOfTwoSemiprimes n ↔ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 22)) := by
  sorry

end OMA.S_oeis_a241656
