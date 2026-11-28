import Mathlib

/-!
# A144247: Prime numbers of the form 11^k ± 10

Source: https://oeis.org/A144247

Conjecture (OEIS A144247):
`131` is the only base-10 palindrome in the sequence of primes of the form `11^k ± 10`
with `k ≥ 1`.

Conventions:
- Offset: `1`; first terms: `131` (`11^2 + 10`), `1321` (`11^3 - 10`), `214358891` (`11^8 + 10`), ...
- Requiring `1 ≤ k` ensures `11^k ≥ 11 > 10` (avoiding `ℕ` subtraction underflow and
  excluding `11^0 + 10 = 11`).
- Base-10 palindromicity is defined via `(Nat.digits 10 p).reverse = Nat.digits 10 p`.
-/

namespace OMA.S_oeis_a144247

/-- Predicate stating that `n` is a base-10 palindrome. -/
def IsPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- The set of primes of the form `11^k - 10` or `11^k + 10` for `k ≥ 1` (OEIS A144247). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ k : ℕ, 1 ≤ k ∧ (p = 11 ^ k - 10 ∨ p = 11 ^ k + 10)}

/-- Conjecture: `131` is the only decimal palindrome in OEIS A144247. -/
theorem main :
    ∀ p : ℕ, p ∈ S → IsPalindrome p → p = 131 := by
  sorry

end OMA.S_oeis_a144247
