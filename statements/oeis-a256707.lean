import Mathlib

/-!
# A256707: Number of unordered ways to write n as the sum of two distinct elements of the set {floor(x/3): 3*x-1 and 3*x+1 are twin primes}.

Source: https://oeis.org/A256707
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A256707): `a(n) > 0` for all `n > 0`. Moreover, for any integer
`m > 10` every positive integer can be written as the sum of two distinct elements of the set
`{floor(x/m) : x - 1 and x + 1 are twin prime}`. (The conjecture implies the Twin Prime Conjecture.)

Formalization notes:
* `floor` of a quotient of natural numbers is natural-number division in `ℕ`.
* "`x - 1` and `x + 1` are twin prime" is stated as `x - 1` and `x + 1` both prime (then `x ≥ 3`,
  so the subtraction is exact); likewise `3x - 1` and `3x + 1` both prime.
* With this definition `a(1), ..., a(12)` = 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, matching the data of
  A256707.
-/

namespace OMA.S_oeis_a256707

/-- `{floor(x/3) : 3x - 1 and 3x + 1 are twin primes}`. -/
def A : Set ℕ :=
  {a | ∃ x : ℕ, (3 * x - 1).Prime ∧ (3 * x + 1).Prime ∧ a = x / 3}

/-- `{floor(x/m) : x - 1 and x + 1 are twin primes}`. -/
def B (m : ℕ) : Set ℕ :=
  {a | ∃ x : ℕ, (x - 1).Prime ∧ (x + 1).Prime ∧ a = x / m}

/-- Sun's conjectures of A256707. -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ n = a + b) ∧
      ∀ m : ℕ, 10 < m → ∀ n : ℕ, 0 < n → ∃ a ∈ B m, ∃ b ∈ B m, a ≠ b ∧ n = a + b := by
  sorry

end OMA.S_oeis_a256707
