import Mathlib

/-!
# MathOverflow 297601: is every positive integer a difference of two powers?

Source: https://mathoverflow.net/questions/297601 (CC BY-SA 4.0).

Question (true or false?): every positive integer is the difference of two powers, e.g.
`1 = 3² - 2³`, `2 = 3³ - 5²`, `3 = 2⁷ - 5³`; the cases `6` and `8` are left open in the post.
A power is `r^i` with integers `r > 0` and `i > 1`, the convention of OEIS A074981 (linked in the
comments), which conjecturally lists the positive integers that are not of the form `r^i - s^j`
with `r, s > 0` and `i, j > 1` (beginning `6, 14, 34, …`).

`main` states the proposition of the post; a disproof exhibits a positive integer that is not a
difference of two such powers.
-/

namespace OMA.S_mo_297601

theorem main : ∀ n : ℕ, 0 < n →
    ∃ r s i j : ℕ, 0 < r ∧ 0 < s ∧ 1 < i ∧ 1 < j ∧ (n : ℤ) = (r : ℤ) ^ i - (s : ℤ) ^ j := by
  sorry

end OMA.S_mo_297601
