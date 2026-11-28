import Mathlib

/-!
# OEIS A329126: number of ones in the least base-independent multiple

Source: https://oeis.org/A329126
`a n` is the least positive number which yields a multiple of `n` when its decimal digits
(necessarily `0`s and `1`s) are read in any base. Conjecture: the number of `1`s in `a n`
is `n`.

Conventions. A digit string is a list `l` of decimal digits (least significant first, as in
`Nat.digits`); "read in base `b`" is `Nat.ofDigits b l`, for every base `b ≥ 2`. `a n` is
the least positive `m` such that `n ∣ Nat.ofDigits b (Nat.digits 10 m)` for all `b ≥ 2`
(taken with `sInf`). `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a329126

/-- A329126. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m | 0 < m ∧ ∀ b ≥ 2, n ∣ Nat.ofDigits b (Nat.digits 10 m)}

theorem main : ∀ n : ℕ, 1 ≤ n → (Nat.digits 10 (a n)).count 1 = n := by
  sorry

end OMA.S_oeis_a329126
