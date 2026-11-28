import Mathlib

/-!
# A088249: Smallest palindromic prime beginning with the n-th prime

Source: https://oeis.org/A088249
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) is the smallest base-10 palindromic prime whose decimal expansion begins
with prime(n), or 0 if no such prime exists.
Conjecture: Except for n = 1 and n = 3, a(n) = 0 if and only if the most
significant decimal digit of prime(n) is in {2, 4, 5, 6, 8}.
-/

namespace OMA.S_oeis_a088249

/-- The `n`-th prime (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The most significant base-10 digit of `m`. -/
def msd10 (m : ℕ) : ℕ :=
  (Nat.digits 10 m).getLastD 0

/-- `p` is a base-10 palindromic prime beginning with `q`. -/
def IsPalindromicPrimeStartingWith (q p : ℕ) : Prop :=
  p.Prime ∧
  (Nat.digits 10 p).reverse = Nat.digits 10 p ∧
  (Nat.digits 10 q).reverse <+: (Nat.digits 10 p).reverse

theorem main :
    ∀ n : ℕ, 1 ≤ n → n ≠ 1 → n ≠ 3 →
      ((¬ ∃ p : ℕ, IsPalindromicPrimeStartingWith (nthPrime n) p) ↔
        msd10 (nthPrime n) ∈ ({2, 4, 5, 6, 8} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a088249
