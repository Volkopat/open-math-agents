import Mathlib

/-!
# A054925: `a(n) = ceiling(n*(n-1)/4)`.

Source: https://oeis.org/A054925
Credit: @cjchaffin

Conjecture (Raul Prisacariu, Sep 01 2024): for `n > 11` there always exists a prime
`p` such that `a(n) < p ≤ a(n+1)`.

Conventions: offset 0; `a n = (n * (n - 1) + 3) / 4` is the standard integer form of
`⌈n(n-1)/4⌉` on the naturals (and matches the listed initial terms, including `a 0 = 0`).
-/

namespace OMA.S_oeis_a054925

/-- `⌈n(n-1)/4⌉`, as an integer quotient `(n*(n-1)+3)/4`. -/
def a (n : ℕ) : ℕ := (n * (n - 1) + 3) / 4

theorem main : ∀ n : ℕ, 11 < n →
    ∃ p : ℕ, p.Prime ∧ a n < p ∧ p ≤ a (n + 1) := by
  sorry

end OMA.S_oeis_a054925
