import Mathlib

/-!
# The greedy squarefree-sum permutation

Start with 1. At each step take the least positive integer that has not
appeared and whose square, added to the preceding term's square, gives a
squarefree integer. The conjecture is that this rule produces a permutation
of the positive integers.

Source: https://oeis.org/A256271 (OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a256271

theorem main : ∃ a : ℕ+ → ℕ+,
    a 1 = 1 ∧
    (∀ n : ℕ+, IsLeast
      {k : ℕ+ | (∀ i : ℕ+, i ≤ n → a i ≠ k) ∧
        Squarefree ((k : ℕ) ^ 2 + (a n : ℕ) ^ 2)}
      (a (n + 1))) ∧
    Function.Bijective a := by
  sorry

end OMA.S_oeis_a256271
