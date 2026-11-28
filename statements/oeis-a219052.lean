import Mathlib

/-!
# A219052

Source: https://oeis.org/A219052
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of ways to write `n = p + q (3 - (-1)ⁿ)/2` with `q ≤ n/2` and `p`, `q`,
`p² + q² - 1` all prime. Conjecture (Zhi-Wei Sun, OEIS): `a(n) > 0` for all `n > 784`.

## Encoding

* `(3 - (-1)ⁿ)/2` is `1` for even `n` and `2` for odd `n`.
* `a(n) > 0` means such primes `p, q` exist; `q ≤ n/2` is `2q ≤ n`; `p² + q² - 1` is computed in
  `ℕ` (it is `≥ 7` for primes `p, q`).
-/

namespace OMA.S_oeis_a219052

/-- `(3 - (-1)ⁿ)/2`. -/
def c (n : ℕ) : ℕ := if n % 2 = 0 then 1 else 2

theorem main :
    ∀ n : ℕ, 784 < n →
      ∃ p q : ℕ, n = p + q * c n ∧ 2 * q ≤ n ∧ p.Prime ∧ q.Prime ∧ (p ^ 2 + q ^ 2 - 1).Prime := by
  sorry

end OMA.S_oeis_a219052
