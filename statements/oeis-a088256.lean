import Mathlib

/-!
# A088256: Primorial numbers k such that both k - 1 and k + 1 are prime

Source: https://oeis.org/A088256

Conjecture (OEIS A088256):
The sequence of primorial numbers `k = p_n#` such that both `k - 1` and `k + 1` are prime
is finite.

Conventions:
- Offset: `1`; known terms include `6 = 2*3`, `30 = 2*3*5`, `2310 = 2*3*5*7*11`.
- `primorial n` is the product of the first `n` primes (`primorial 0 = 1`, `primorial 1 = 2`,
  `primorial 2 = 6`, `primorial 3 = 30`, ...).
-/

namespace OMA.S_oeis_a088256

/-- The `n`-th primorial `p_n#`, product of the first `n` primes. -/
noncomputable def primorial (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- The set of primorials `k` such that `k - 1` and `k + 1` are both prime (OEIS A088256). -/
def S : Set ℕ :=
  {k : ℕ | (∃ n : ℕ, k = primorial n) ∧ Nat.Prime (k - 1) ∧ Nat.Prime (k + 1)}

/-- Conjecture: there are only finitely many primorials `k` with both `k - 1` and `k + 1` prime. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a088256
