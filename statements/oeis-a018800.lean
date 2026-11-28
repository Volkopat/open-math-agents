import Mathlib

/-!
# OEIS A018800: the smallest prime beginning with n

Source: https://oeis.org/A018800
`a n` is the smallest prime whose decimal expansion begins with that of `n`. Conjecture: if
`a(n)` is `n` concatenated with `k`, then `k < n`.

Conventions. "Begins with `n`" means `p = n · 10^d + k` with `d ≥ 0` and `0 ≤ k < 10^d` (the
appended block may have leading zeros; `d = 0` means `p = n`). For `a n` written this way
(with the `d` determined by the number of digits of `a n` and `n`), the conjecture is `k < n`.
`n ≥ 2`: for `n = 1`, `a 1 = 11` has `k = 1 = n`, so the conjecture is read for `n ≥ 2`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a018800

/-- `p` begins with `n` in decimal, with appended block `k` of `d` digits. -/
def BeginsWith (n p d k : ℕ) : Prop := k < 10 ^ d ∧ p = n * 10 ^ d + k

/-- The smallest prime beginning with `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {p | p.Prime ∧ ∃ d k, BeginsWith n p d k}

theorem main : ∀ n : ℕ, 2 ≤ n → ∀ d k : ℕ, BeginsWith n (a n) d k → k < n := by
  sorry

end OMA.S_oeis_a018800
