import Mathlib

/-!
# A220091: Number of ways to write n=p+q+(n mod 2)q with p>q and p, q, 6q-1, 6q+1 all prime.

Source: https://oeis.org/A220091
Credit: @eltociear

`a(n)` (offset 1) counts the ways to write `n = p + q + (n mod 2) q` with `p > q` and `p`, `q`,
`6q - 1`, `6q + 1` all prime; so `n = p + q` for even `n` and `n = p + 2q` for odd `n`
(`a(31) = 1` from `31 = 17 + 2·7`). The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all even n >= 8070 and odd n >= 18680.

`main` states that such `p`, `q` exist for every even `n ≥ 8070` and every odd `n ≥ 18680`.
`6q - 1` is an exact natural-number subtraction since `q ≥ 2`.
-/

namespace OMA.S_oeis_a220091

/-- The conjecture in OEIS A220091: `a(n) > 0` for even `n ≥ 8070` and odd `n ≥ 18680`. -/
theorem main : ∀ n : ℕ, ((Even n ∧ 8070 ≤ n) ∨ (Odd n ∧ 18680 ≤ n)) →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ q < p ∧ (6 * q - 1).Prime ∧ (6 * q + 1).Prime ∧
      n = p + q + (n % 2) * q := by
  sorry

end OMA.S_oeis_a220091
