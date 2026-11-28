import Mathlib

/-!
# A343268: Numbers that are not the sum of exactly four terms from A020330 (not necessarily distinct).

Source: https://oeis.org/A343268
Credit: @keiichisince1986-bot

A343268 is the sequence `a(n)` named in the title. The entry states:
Madhusudan et al. (2018) conjectured that a(112) = 1772 is the last term of this sequence.

Conventions:
- A020330 lists the numbers whose binary representation is two copies of the same string: `m (2^k + 1)` with
  `2^(k-1) ≤ m < 2^k`, `k ≥ 1` (the string is the `k`-bit binary representation of `m`). `IsBinSquare a`.
- The sequence is finite with last term `1772` exactly when `1772` is the greatest element of the set:
  `IsGreatest S 1772`.
-/

namespace OMA.S_oeis_a343268

/-- `a` is a term of A020330: its binary representation is a string written twice. -/
def IsBinSquare (a : ℕ) : Prop := ∃ k m : ℕ, 1 ≤ k ∧ 2 ^ (k - 1) ≤ m ∧ m < 2 ^ k ∧ a = m * (2 ^ k + 1)

theorem main :
    IsGreatest {n : ℕ | ¬ ∃ a b c d : ℕ, IsBinSquare a ∧ IsBinSquare b ∧ IsBinSquare c ∧ IsBinSquare d ∧
      a + b + c + d = n} 1772 := by
  sorry

end OMA.S_oeis_a343268
