import Mathlib

/-!
# OEIS A088112: perfect powers whose digit reversal is prime

Source: https://oeis.org/A088112
Perfect powers whose decimal digit reversal is prime. Conjectures: (1) the sequence is
infinite; (2) for every `n` there are infinitely many members of the form `k^n`. `main` is
their conjunction.

Conventions. A perfect power is `k^n` with `k ≥ 2`, `n ≥ 2`; in (2), `n ≥ 2`. The reversal of
`m` is the number whose decimal digits are those of `m` in reverse order.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a088112

/-- Decimal digit reversal. -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

theorem main :
    {m : ℕ | (∃ k n : ℕ, 2 ≤ k ∧ 2 ≤ n ∧ m = k ^ n) ∧ (rev m).Prime}.Infinite ∧
      ∀ n : ℕ, 2 ≤ n → {k : ℕ | 2 ≤ k ∧ (rev (k ^ n)).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a088112
