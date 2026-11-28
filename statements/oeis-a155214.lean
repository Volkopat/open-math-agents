import Mathlib

/-!
# A155214: Palindromes n of the form p + prime(p) for some prime p

Source: https://oeis.org/A155214

Conjecture (OEIS A155214):
There are infinitely many base-10 palindromes `n` that can be written as
`n = p + prime(p)` for some prime `p`.

Conventions:
- Offset: `1`; first terms: `5, 8, 424, 606, 666, 2552, ...`
  (e.g., `2 + prime(2) = 2 + 3 = 5`, `3 + prime(3) = 3 + 5 = 8`).
- `nthPrime k` is the `k`-th prime (`1`-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...),
  defined via `Nat.nth Nat.Prime (k - 1)`.
-/

namespace OMA.S_oeis_a155214

/-- The `k`-th prime number (`1`-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Predicate stating that `n` is a base-10 palindrome. -/
def IsPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- The set of base-10 palindromes of the form `p + prime(p)` for some prime `p`
(OEIS A155214). -/
def S : Set ℕ :=
  {n : ℕ | IsPalindrome n ∧ ∃ p : ℕ, Nat.Prime p ∧ n = p + nthPrime p}

/-- Conjecture: the sequence A155214 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a155214
