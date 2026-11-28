import Mathlib

/-!
# A289629: Smallest positive k such that (k+1)^n + (-k)^n is divisible by a square greater than 1.

Source: https://oeis.org/A289629
Credit: @luciusacarr

The entry's conjecture (Kevin P. Thompson, Dec 03 2021): "(k+1)^n + (-k)^n is not squarefree for
the following (n, k) patterns, with m >= 1: (22m-11, 2), (20m-6, 3), (20m-2, 3), (3^m, 7),
(15m, 7), (20m-15, 14), (16m-8, 19), (42m-35, 23), and (8m-4, 113)." (The same comment block
also records the proved fact a(20m+10) = 1, since 5^2 divides 2^(20m+10) + 1; that remark is not
the conjecture and is not part of this statement. The accompanying remark that a(n) is "usually"
the listed k is informal and is not formalized either.)

Reading of the source:
* `E(n, k) = (k+1)^n + (-k)^n` is computed in `ℤ`; "not squarefree" is `¬ Squarefree` in `ℤ`
  (equivalently: divisible by the square of an integer greater than 1).
* The conjecture is the conjunction of the nine patterns, each for every `m ≥ 1`.
-/

namespace OMA.S_oeis_a289629

/-- `(k+1)^n + (-k)^n`. -/
def E (n k : ℕ) : ℤ := ((k : ℤ) + 1) ^ n + (-(k : ℤ)) ^ n

theorem main :
    ∀ m : ℕ, 1 ≤ m →
      ¬ Squarefree (E (22 * m - 11) 2) ∧ ¬ Squarefree (E (20 * m - 6) 3) ∧
      ¬ Squarefree (E (20 * m - 2) 3) ∧ ¬ Squarefree (E (3 ^ m) 7) ∧
      ¬ Squarefree (E (15 * m) 7) ∧ ¬ Squarefree (E (20 * m - 15) 14) ∧
      ¬ Squarefree (E (16 * m - 8) 19) ∧ ¬ Squarefree (E (42 * m - 35) 23) ∧
      ¬ Squarefree (E (8 * m - 4) 113) := by
  sorry

end OMA.S_oeis_a289629
