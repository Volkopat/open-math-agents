import Mathlib

/-!
# A182755: Expansion of (1+35*x)/(1-90*x^2).

Source: https://oeis.org/A182755
Credit: @agchua

Comment line of A182755 (entry by Jaroslav Krizek, Nov 27 2010), verbatim:
  a(1) = 1, a(2) = 35, for n >= 3; a(n) = the smallest number h > a(n-1) such that
  [[a(n-2) + a(n-1)] * [a(n-2) + h] * [a(n-1) + h]] / [a(n-2) * a(n-1) * h] is an integer
  (= 130). (conjectured)

Offset 1. The definition below is the coefficient sequence of (1+35x)/(1-90x^2), indexed from 1:
multiplying by 1-90x^2 gives a(1) = 1, a(2) = 35 and a(n) = 90*a(n-2) for n >= 3 (the entry's
programs use the same recurrence; closed form a(2n) = 35*90^(n-1), a(2n+1) = 90^n). The value
a 0 = 0 is a placeholder outside the offset and is never used.
The statement says, for every n >= 3: a(n) is the least natural number h > a(n-1) such that
a(n-2)*a(n-1)*h divides (a(n-2)+a(n-1))*(a(n-2)+h)*(a(n-1)+h) (all terms are positive, so this
says that the quotient is an integer), and for h = a(n) the quotient equals 130.
-/

namespace OMA.S_oeis_a182755

/-- A182755 with offset 1: a(1) = 1, a(2) = 35, a(n) = 90*a(n-2) for n >= 3. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 35
  | (n + 3) => 90 * a (n + 1)

/-- The comment-line conjecture of A182755, for every n >= 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    IsLeast {h : ℕ | a (n - 1) < h ∧
        a (n - 2) * a (n - 1) * h ∣ (a (n - 2) + a (n - 1)) * (a (n - 2) + h) * (a (n - 1) + h)}
      (a n) ∧
    (a (n - 2) + a (n - 1)) * (a (n - 2) + a n) * (a (n - 1) + a n) =
      130 * (a (n - 2) * a (n - 1) * a n) := by
  sorry

end OMA.S_oeis_a182755
