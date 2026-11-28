import Mathlib

/-!
# MathOverflow 315770: is `∑_{d ∣ n} 1/(d+1)` never an integer?

Source: https://mathoverflow.net/questions/315770 (Zhi-Wei Sun, CC BY-SA 4.0).

Conjecture (i) of the post begins: `∑_{d ∣ n} 1/(d+1) ∉ ℤ` for all `n = 1, 2, 3, …`, the sum
running over the positive divisors `d` of `n` (checked by the asker for `n ≤ 2·10⁵`). The post
goes on to further conjectures (distinct fractional parts of `∑_{d ∣ n} 1/(d+m)^k`, and of
`∑_{d ∣ n} 1/d^k`); we state only this first one, which is the question of the title.
-/

namespace OMA.S_mo_315770

theorem main : ∀ n : ℕ, 0 < n → ∀ z : ℤ, ∑ d ∈ n.divisors, (1 : ℚ) / ((d : ℚ) + 1) ≠ z := by
  sorry

end OMA.S_mo_315770
