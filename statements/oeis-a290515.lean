import Mathlib

/-!
# A290515: a(n) = smallest number that is the start of a gap of size n between successive prime powers (A000961), or 0 if no such number exists.

Source: https://oeis.org/A290515
Credit: @keiichisince1986-bot

A290515 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) always exists.

Conventions:
- A000961 lists `1` and the prime powers `p^k` (`k ≥ 1`): `IsPPowOrOne m`, with Mathlib's `IsPrimePow`.
- A gap of size `n` between successive terms starts at `a` when `a` and `a + n` are terms and no number
  strictly between them is a term. The offset is `1`, so `n ≥ 1`.
-/

namespace OMA.S_oeis_a290515

/-- `m` is a term of A000961: `1` or a prime power. -/
def IsPPowOrOne (m : ℕ) : Prop := m = 1 ∨ IsPrimePow m

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ a : ℕ, IsPPowOrOne a ∧ IsPPowOrOne (a + n) ∧
      ∀ b : ℕ, a < b → b < a + n → ¬ IsPPowOrOne b := by
  sorry

end OMA.S_oeis_a290515
