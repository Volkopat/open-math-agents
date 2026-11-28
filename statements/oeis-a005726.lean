import Mathlib

/-!
# OEIS A005726: quadrinomial coefficients, a D-finite recurrence

Source: https://oeis.org/A005726
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = ∑_{k=0}^{⌊n/2⌋} C(n, k) C(n, 2k+1)` (`n ≥ 1`): `1, 2, 6, 20, 65, …`. Conjecture (Mathar,
2012): `2(n-1)(2n+1)(13n-14) a(n) + (-143n³ + 297n² - 148n + 12) a(n-1)
  - 4(n-1)(26n² - 41n + 9) a(n-2) - 16(n-1)(n-2)(13n-1) a(n-3) = 0`.

Conventions:
* `a` is given by Barry's formula from the entry (offset `1`), computed in `ℤ`. The recurrence
  involves `a(n-3)`, so it is stated for `n ≥ 4`.
-/

namespace OMA.S_oeis_a005726

/-- Quadrinomial coefficients. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n / 2 + 1), (n.choose k * n.choose (2 * k + 1) : ℕ)

/-- Mathar's recurrence for `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    let m : ℤ := n
    2 * (m - 1) * (2 * m + 1) * (13 * m - 14) * a n +
      (-143 * m ^ 3 + 297 * m ^ 2 - 148 * m + 12) * a (n - 1) -
      4 * (m - 1) * (26 * m ^ 2 - 41 * m + 9) * a (n - 2) -
      16 * (m - 1) * (m - 2) * (13 * m - 1) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a005726
