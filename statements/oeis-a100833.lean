import Mathlib

/-!
# The least positive palindrome-free and squarefree word

John W. Layman's sequence and Robert Israel's 2019 conjecture, https://oeis.org/A100833.
https://oeis.org/A007814 is the 2-adic valuation of a positive integer.
Credit: @frido22
-/

namespace OMA.S_oeis_a100833

/-- In the one-based prefix ending at `n`, every suffix of length at least two
has a mismatching mirror pair, and every nonempty even-length suffix has a
mismatching pair between its two halves. -/
def AllowedEnd (w : ℕ → ℕ) (n : ℕ) : Prop :=
  (∀ s, 0 < s → s < n → ∃ i, s ≤ i ∧ i ≤ n ∧ w i ≠ w (s + n - i)) ∧
  (∀ d, 0 < d → 2 * d ≤ n → ∃ i, n - d < i ∧ i ≤ n ∧ w i ≠ w (i - d))

/-- Append the least positive letter that creates no forbidden suffix.
Earlier factors have already been checked in their own prefixes. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else sInf {c : ℕ | 0 < c ∧
    AllowedEnd (fun i => if _h : i < n ∧ 0 < i then a i else c) n}
termination_by n
decreasing_by exact _h.1

/-- Israel's formula for all indices of A100833, starting at 1. -/
theorem main : ∀ n : ℕ, 0 < n → a n =
    if n % 3 = 1 then 1 else if n % 3 = 2 then 2 else 3 + padicValNat 2 (n / 3) := by
  sorry

end OMA.S_oeis_a100833
