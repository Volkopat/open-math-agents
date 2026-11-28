import Mathlib

/-!
# A237837: a prime p < n with a cube number of Sophie Germain primes up to n - p

Source: https://oeis.org/A237837
Credit: @coleman415

The sequence (Zhi-Wei Sun) is: `a(n)` = number of primes `p < n` such that the number of Sophie
Germain primes among `1, ..., n-p` is a cube.
The entry records: *Conjecture: a(n) > 0 for all n > 53.*

So the conjecture says: for every `n > 53` there is a prime `p < n` such that the number of
Sophie Germain primes among `1, ..., n - p` is a cube.

Conventions:
- A Sophie Germain prime is a prime `q` with `2q + 1` also prime (2, 3, 5, 11, 23, 29, ...).
- `0` and `1` count as cubes (the entry's example uses `1^3 = 1`). A cube is `x^3` with `x` a
  natural number.
- Since `p < n`, the natural-number subtraction `n - p` is the integer difference.
-/

namespace OMA.S_oeis_a237837

/-- The number of Sophie Germain primes among `1, ..., m`. -/
def sophieGermainCount (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter fun q => q.Prime ∧ (2 * q + 1).Prime).card

/-- The conjecture of OEIS A237837. -/
theorem main :
    ∀ n : ℕ, 53 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ ∃ x : ℕ, sophieGermainCount (n - p) = x ^ 3 := by
  sorry

end OMA.S_oeis_a237837
