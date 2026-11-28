import Mathlib

/-!
# A060064: First subsequent, disjoint occurrence of n consecutive nonprimes.

Source: https://oeis.org/A060064
Credit: @eltociear

`a(1) = 4`, and `a(n + 1)` is the least `s` greater than `a(n) + n - 1` (the end of the previous
block) such that the `n + 1` consecutive integers `s, s + 1, …, s + n` are all nonprime
(`4; 8, 9; 14, 15, 16; 24, …, 27; …`, so the sequence is `4, 8, 14, 24, 32, 90, ...`). The entry
conjectures (Robert Israel, May 04 2025):

  a(n) - 1 is always prime.

`main` states that `a(n) - 1` is prime for every `n ≥ 1`. `a 0` is a placeholder `0`.
-/

namespace OMA.S_oeis_a060064

/-- OEIS A060064, with the placeholder `a 0 = 0`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 4
  | n + 2 => sInf {s : ℕ | a (n + 1) + n < s ∧ ∀ i < n + 2, ¬ (s + i).Prime}

/-- The conjecture in OEIS A060064: `a(n) - 1` is prime for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n - 1).Prime := by
  sorry

end OMA.S_oeis_a060064
