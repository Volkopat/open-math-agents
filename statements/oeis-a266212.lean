import Mathlib

/-!
# OEIS A266212: x^4 - y^3 + z^2 = m has infinitely many positive solutions

Source: https://oeis.org/A266212
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A266212 lists the positive integers `x` such that `x³ = y⁴ + z²` for some positive integers `y`
and `z`.

Conjecture: for any integer `m`, there are infinitely many triples `(x, y, z)` of positive
integers with `x⁴ - y³ + z² = m`.

Formalization notes:
* The equation is read in `ℤ`; "infinitely many triples" is stated as: the set of solution
  triples of positive integers is infinite.
-/

namespace OMA.S_oeis_a266212

/-- For every integer `m`, `x⁴ - y³ + z² = m` has infinitely many solutions in positive
integers. -/
theorem main :
    ∀ m : ℤ, {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
      (t.1 : ℤ) ^ 4 - (t.2.1 : ℤ) ^ 3 + (t.2.2 : ℤ) ^ 2 = m}.Infinite := by
  sorry

end OMA.S_oeis_a266212
