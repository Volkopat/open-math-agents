import Mathlib

/-!
# Consecutive Sierpiński numbers (OEIS A270994)

Source: https://oeis.org/A270994 (OEIS Foundation, CC BY-SA 4.0).
Altug Alkan asks whether every term and the term plus 28 are consecutive
Sierpiński numbers. The sequence starts at index 0.

Tom Adamczewski's *OEIS Open*, Appendix A (https://arxiv.org/abs/2608.11941),
reports an intermediate Sierpiński number at index 162178349052694.
-/

namespace OMA.S_oeis_a270994

/-- A Sierpiński number is an odd positive integer `k` for which
`k * 2 ^ m + 1` is composite for every positive integer `m`. -/
def IsSierpinski (k : ℕ) : Prop :=
  Odd k ∧ ∀ m : ℕ, 0 < m → ¬ Nat.Prime (k * 2 ^ m + 1)

/-- The arithmetic progression in OEIS A270994. -/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

theorem main : ∀ n : ℕ,
    IsSierpinski (a n) ∧ IsSierpinski (a n + 28) ∧
      ∀ k : ℕ, a n < k → k < a n + 28 → ¬ IsSierpinski k := by
  sorry

end OMA.S_oeis_a270994
