import Mathlib

/-!
# A079278: Denominator of b(n) where b(1) = 1, b(n) = b(n-1) + 1/(1 + 1/b(n-1))

Source: https://oeis.org/A079278
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Define a rational sequence {b(n)} as b(1) = 1, b(n) = b(n-1) + 1/(1 + 1/b(n-1)) for n > 1;
a(n) is the denominator of b(n).
Conjecture (OEIS entry): a(m+1) = a(m)^2 + a(m)^3 / a(m-1)^2 - a(m)*a(m-1)^2 for m >= 2.
-/

namespace OMA.S_oeis_a079278

def b : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 => b (n + 1) + 1 / (1 + 1 / b (n + 1))

def a (n : ℕ) : ℕ := (b n).den

theorem main :
    ∀ m : ℕ, 2 ≤ m →
      (a (m + 1) : ℚ) =
        (a m : ℚ) ^ 2 + (a m : ℚ) ^ 3 / (a (m - 1) : ℚ) ^ 2 -
          (a m : ℚ) * (a (m - 1) : ℚ) ^ 2 := by
  sorry

end OMA.S_oeis_a079278
