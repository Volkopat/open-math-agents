import Mathlib

/-!
# A399572: Triangular numbers in the Padovan sequence A000931.

Source: https://oeis.org/A399572
Credit: @keiichisince1986-bot

A399572 lists the triangular numbers that occur in the Padovan sequence A000931:
`0, 1, 3, 21, 28, 351, 465, 1081`.
The entry notes that the sequence is finite (by a theorem of Corvaja and Zannier) and states:
Conjecture: the sequence is complete (no further terms among `A000931(k)` for `k ≤ 10^12`).

Conventions:
- `padovan` is A000931: `a(0) = 1, a(1) = 0, a(2) = 0` and `a(n) = a(n-2) + a(n-3)`, i.e.
  `padovan (n + 3) = padovan (n + 1) + padovan n`. Its first values are
  `1, 0, 0, 1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, …`.
- A triangular number is `k * (k + 1) / 2` for some `k : ℕ` (A000217); `0` is triangular.
- Complete means that the data list every term, so the conjecture says that the set of values of
  the Padovan sequence that are triangular is exactly `{0, 1, 3, 21, 28, 351, 465, 1081}`.
-/

namespace OMA.S_oeis_a399572

/-- The Padovan sequence A000931. -/
def padovan : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | n + 3 => padovan (n + 1) + padovan n

theorem main :
    {m : ℕ | (∃ n : ℕ, m = padovan n) ∧ ∃ k : ℕ, m = k * (k + 1) / 2} =
      {0, 1, 3, 21, 28, 351, 465, 1081} := by
  sorry

end OMA.S_oeis_a399572
