import Mathlib

/-!
# OEIS A047239: the numbers 1, 2 mod 6 are the greedy sequence avoiding sums of three terms

Source: https://oeis.org/A047239 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A047239 (N. J. A. Sloane), offset 1: Numbers that are congruent to {1, 2} (mod 6).
Formula: a(n) = 3*(n-1) - (-1)^n. - Rolf Pleisch, Aug 04 2009. Comment: Conjecture: a(n) is the
least positive integer > a(n-1) that is not equal to a(i) + a(j) + a(k) for any i <= j <= k <= n.
- Clark Kimberling, Oct 09 2019

Formalization notes:
* a(n) is given by the entry's formula 3*(n-1) - (-1)^n, that is 3n - 2 for odd n and 3n - 4 for
  even n; for n = 1, 2, 3, ... these are the numbers congruent to 1 or 2 mod 6 in increasing
  order. The value at n = 0 is not used.
* The statement is for every n >= 2, since a(n-1) must exist. The indices i, j, k range over
  1 <= i <= j <= k <= n as in the comment, so k = n is allowed.
* Controls from the entry: the definition gives 1, 2, 7, 8, 13, 14, 19, 20 for n = 1..8.
-/

namespace OMA.S_oeis_a047239

/-- A047239(n), offset 1 (the value at 0 is unused). -/
def a (n : ℕ) : ℕ := if n % 2 = 1 then 3 * n - 2 else 3 * n - 4

/-- The candidates at step n: positive integers above a(n-1) that are no sum a(i)+a(j)+a(k). -/
def Cand (n m : ℕ) : Prop :=
  0 < m ∧ a (n - 1) < m ∧ ∀ i j k, 1 ≤ i → i ≤ j → j ≤ k → k ≤ n → m ≠ a i + a j + a k

/-- Kimberling's conjecture: for n >= 2, a(n) is the least candidate. -/
theorem main : ∀ n : ℕ, 2 ≤ n → IsLeast {m | Cand n m} (a n) := by
  sorry

end OMA.S_oeis_a047239
