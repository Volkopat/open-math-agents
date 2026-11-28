import Mathlib

/-!
# A048270: Infinitely many chained prime-leg/prime-hypotenuse Pythagorean triangles

Source: https://oeis.org/A048270
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A048270: Sequence of 2 Pythagorean triangles, each with a leg and hypotenuse prime.
The leg of the second triangle is the hypotenuse of the first.

Statement:
It is conjectured that there are infinitely many such pairs of triangles.

Conventions:
- A pair of such Pythagorean triangles corresponds to primes `p, q, r` and positive integers
  `b, c` satisfying `p^2 + b^2 = q^2` and `q^2 + c^2 = r^2`.
-/

namespace OMA.S_oeis_a048270

theorem main :
    Set.Infinite {t : ℕ × ℕ × ℕ × ℕ × ℕ |
      let (p, b, q, c, r) := t
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ 0 < b ∧ 0 < c ∧
      p ^ 2 + b ^ 2 = q ^ 2 ∧ q ^ 2 + c ^ 2 = r ^ 2} := by
  sorry

end OMA.S_oeis_a048270
