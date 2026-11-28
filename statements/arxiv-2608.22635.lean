import Mathlib

namespace OMA.S_arxiv_2608_22635

/-- Dujella's conjecture on integral points on the elliptic curve attached to a Diophantine triple
(arXiv:2608.22635): for every Diophantine triple `{a, b, c}` of distinct positive integers with
`ab + 1 = r^2`, `ac + 1 = s^2`, `bc + 1 = t^2` (`r, s, t : ℕ`), every integral point `(x, y)` on
`y^2 = (a x + 1)(b x + 1)(c x + 1)` has `x`-coordinate in `{0, d_-, d_+}`, together with `-1` when
the triple contains `1`, where `d_± = a + b + c + 2abc ± 2rst`. -/
theorem main :
    ∀ (a b c r s t : ℕ),
      0 < a → 0 < b → 0 < c → a ≠ b → a ≠ c → b ≠ c →
      a * b + 1 = r ^ 2 → a * c + 1 = s ^ 2 → b * c + 1 = t ^ 2 →
      ∀ (x y : ℤ),
        y ^ 2 = ((a : ℤ) * x + 1) * ((b : ℤ) * x + 1) * ((c : ℤ) * x + 1) →
        x = 0 ∨
        x = (a : ℤ) + b + c + 2 * a * b * c - 2 * r * s * t ∨
        x = (a : ℤ) + b + c + 2 * a * b * c + 2 * r * s * t ∨
        ((a = 1 ∨ b = 1 ∨ c = 1) ∧ x = -1) := by
  sorry

end OMA.S_arxiv_2608_22635
