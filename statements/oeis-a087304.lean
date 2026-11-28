import Mathlib.Data.Nat.Digits.Lemmas

/-!
# OEIS A087304

The $n$th term is the least positive multiple of $n$ which is not $10^k n$
for any $k \ge 0$ and whose product of nonzero decimal digits is the same as
that of $n$, or zero if no such multiple exists. The conjecture that no
term is zero is expressed by existence of an admissible multiple.

Source: https://oeis.org/A087304
-/

namespace OMA.S_oeis_a087304

/-- The product of the nonzero decimal digits of a natural number. -/
def digitProduct (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).map fun d => if d = 0 then 1 else d).prod

theorem main : ∀ n : ℕ, 0 < n →
    ∃ m : ℕ, n < m ∧ n ∣ m ∧ (∀ k : ℕ, m ≠ 10 ^ k * n) ∧
      digitProduct m = digitProduct n := by
  sorry

end OMA.S_oeis_a087304
