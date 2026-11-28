import Mathlib

/-!
# A282971: Number of compositions (ordered partitions) of n into primes of form x^2 + y^2 (A002313).

Source: https://oeis.org/A282971
Credit: @luciusacarr

Conjecture (from the entry): every number > 16 is the sum of at most 4 primes of form
x^2 + y^2. `main` states it.

Reading of the source:
* A002313 are the primes of the form `x^2 + y^2` (with `x, y` natural numbers): 2, 5, 13, 17,
  29, ..., equivalently the primes congruent to 1 or 2 mod 4, as the entry notes.
* "Sum of at most 4" means a sum of `r ≤ 4` such primes, repetitions allowed (the summands are
  indexed by `Fin r`).
* Checked numerically for every n from 17 to 30000 (16 itself needs more than 4 parts).
-/

namespace OMA.S_oeis_a282971

/-- `p` is a prime of the form `x^2 + y^2` (A002313). -/
def IsSumTwoSqPrime (p : ℕ) : Prop := p.Prime ∧ ∃ x y : ℕ, p = x ^ 2 + y ^ 2

theorem main :
    -- Every number > 16 is the sum of at most 4 primes of the form x^2 + y^2.
    ∀ n : ℕ, 16 < n → ∃ (r : ℕ) (b : Fin r → ℕ), r ≤ 4 ∧
      (∀ i, IsSumTwoSqPrime (b i)) ∧ ∑ i, b i = n := by
  sorry

end OMA.S_oeis_a282971
