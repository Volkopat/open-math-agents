import OMAStatements.S_oeis_a298076
import Mathlib

/-!
# A298076: Ordowski's equivalence fails for the negative base `b = -2` and `n = 4`

Here `(b ^ 4 - 1) / (b - 1) = 15 / (-3) = -5`, whose positive divisors `1` and `5` are both
`≡ 1 (mod 4)`, so the left-hand side of the claimed equivalence holds.  But the right-hand side
requires `|b| ^ 4 ≡ |b| (mod 4)`, i.e. `16 % 4 = 2 % 4`, which is false.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298076.main) := by
  intro h
  have h4 := h (-2) (by decide) 4 (by norm_num) (by decide)
  have hval : (((-2 : ℤ) ^ 4 - 1) / (-2 - 1)).natAbs = 5 := by decide
  rw [hval] at h4
  -- the left-hand side holds: the divisors of `5` are `1` and `5`
  have hleft : ∀ d : ℕ, d ∣ 5 → d % 4 = 1 := by
    intro d hd
    have hle : d ≤ 5 := Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> first | rfl | (exfalso; revert hd; decide)
  -- but the right-hand side would give `16 % 4 = 2 % 4`
  have hright := (h4.mp hleft).1
  revert hright
  decide
