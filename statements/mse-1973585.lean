import Mathlib

/-!
# Is there a base in which only finitely many palindromes are prime?

Source: https://math.stackexchange.com/questions/1973585

Can we prove that there must be a base `b` such that only finitely many palindromes in base `b`
are primes?

`main` states the affirmative: for some base `b ≥ 2`, only finitely many primes are palindromes
in base `b`. (Comments expect the answer to be negative.)

Formalization notes:
* `n` is a palindrome in base `b` when its list of base-`b` digits (`Nat.digits`, without leading
  zeros) reads the same reversed.
-/

namespace OMA.S_mse_1973585

/-- `n` is a palindrome in base `b`. -/
def IsPalindrome (b n : ℕ) : Prop := (Nat.digits b n).reverse = Nat.digits b n

/-- Some base `b ≥ 2` has only finitely many palindromic primes. -/
theorem main : ∃ b : ℕ, 2 ≤ b ∧ {p : ℕ | p.Prime ∧ IsPalindrome b p}.Finite := by
  sorry

end OMA.S_mse_1973585
