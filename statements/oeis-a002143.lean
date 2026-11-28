import Mathlib

/-!
# OEIS A002143: a cosecant formula for class numbers

Source: https://oeis.org/A002143
`A002143` lists the class numbers `h(-p)` of `ℚ(√-p)` for primes `p ≡ 3 (mod 4)`.
Conjecture (Zhi-Wei Sun): for every prime `p > 3` with `p ≡ 3 (mod 8)`,
`2 h(-p) √p = ∑_{k=1}^{(p-1)/2} csc(2π k²/p)`.

Conventions. `h(D)` for a negative discriminant `D` is the number of reduced primitive
positive definite binary quadratic forms `(a, b, c)` with `b² - 4ac = D`: `|b| ≤ a ≤ c`,
`gcd(a, b, c) = 1`, and `b ≥ 0` whenever `|b| = a` or `a = c`. For `D = -p` with `p > 3`
prime this is the class number of `ℚ(√-p)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a002143

open Real

/-- The number of reduced primitive positive definite forms of discriminant `D < 0`. -/
noncomputable def h (D : ℤ) : ℕ :=
  ((Finset.Icc (1 : ℤ) D.natAbs ×ˢ Finset.Icc (-(D.natAbs : ℤ)) D.natAbs ×ˢ
      Finset.Icc (1 : ℤ) D.natAbs).filter fun t =>
    t.2.1 ^ 2 - 4 * t.1 * t.2.2 = D ∧ |t.2.1| ≤ t.1 ∧ t.1 ≤ t.2.2 ∧
      Int.gcd (Int.gcd t.1 t.2.1) t.2.2 = 1 ∧
      ((|t.2.1| = t.1 ∨ t.1 = t.2.2) → 0 ≤ t.2.1)).card

theorem main :
    ∀ p : ℕ, p.Prime → 3 < p → p % 8 = 3 →
      2 * (h (-(p : ℤ)) : ℝ) * √p =
        ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), 1 / sin (2 * π * (k : ℝ) ^ 2 / p) := by
  sorry

end OMA.S_oeis_a002143
