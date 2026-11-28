import Mathlib

/-!
# A005563: a(n) = n*(n+2) = (n+1)^2 - 1.

Source: https://oeis.org/A005563
Credit: @cjchaffin

Erdős conjectured (stated on the OEIS page) that `n^2 - 1 = k!` has a solution if and only if
`n` is 5, 11 or 71 (when `k` is 4, 5 or 7).

Conventions:
- The variables `n` and `k` range over the natural numbers (including 0). The three solutions
  listed on the page are positive, and there is no solution with `n = 0` or `k = 0`. Negative
  integers `n` would only repeat the same squares, so they are not included.
- The equation is written `n ^ 2 = k.factorial + 1`, which is equivalent to `n^2 - 1 = k!` in
  the natural numbers and avoids the truncated subtraction `0 - 1` at `n = 0`. The three
  listed pairs do satisfy the equation: `5^2 = 4! + 1`, `11^2 = 5! + 1`, `71^2 = 7! + 1`.
- A second, informal comment on the page about sieving `(n+1)..a(n)` is not formalized here.
-/

namespace OMA.S_oeis_a005563

theorem main : ∀ n k : ℕ,
    n ^ 2 = k.factorial + 1 ↔ n = 5 ∧ k = 4 ∨ n = 11 ∧ k = 5 ∨ n = 71 ∧ k = 7 := by
  sorry

end OMA.S_oeis_a005563
