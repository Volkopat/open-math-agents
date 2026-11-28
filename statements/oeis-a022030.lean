import Mathlib

/-!
# A022030: For even n, a(n+2) is the greatest integer such that a(n+2)/a(n+1) < a(n+1)/a(n); for odd n, the least integer such that a(n+2)/a(n+1) > a(n+1)/a(n); a(0) = 4, a(1) = 16.

Source: https://oeis.org/A022030
Credit: @agchua

Two conjectures in A022030:
  Conjecture: a(n) = 4*a(n-1)-a(n-3)+a(n-4). G.f. = (4-x^2+x^3)/(1-4*x+x^3-x^4). - Colin Barker,
  Feb 16 2012 (formula section)
  Original definition: a(n+2) is the greatest integer such that a(n+2)/a(n+1) < a(n+1)/a(n).
  This original definition would lead to sequence 4, 16, 63, 248, 976, 3841, ... which agrees to over
  2000 terms with the conjectured g.f. = (4 - x^2)/(1 - 4*x + x^3). - M. F. Hasler, Feb 11 2016
  (comment section)
The entry also cites a proof abstract: Tom Adamczewski, OEIS Open: How many conjectures can language
models turn into theorems?, arXiv:2608.11941 [cs.AI], 2026, p. 22 (Appendix A); the entry itself gives
no proof.
This file states all of it (offset 0): Barker's recurrence for n ≥ 4 (all indices are terms) and his
g.f. as an identity of formal power series over ℚ, (∑ a(n) X^n) * (1 - 4X + X^3 - X^4) = 4 - X^2 + X^3;
and Hasler's g.f. for the sequence t of the original definition,
(∑ t(n) X^n) * (1 - 4X + X^3) = 4 - X^2.
Definitions: for positive terms, the greatest integer k with k/a(n+1) < a(n+1)/a(n) is
ceiling(a(n+1)^2/a(n)) - 1, and the least integer k with k/a(n+1) > a(n+1)/a(n) is
floor(a(n+1)^2/a(n)) + 1. These are the formulas of M. F. Hasler (Feb 11 2016) in the entry, a(n) =
ceiling(a(n-1)^2/a(n-2))-1 for even n > 0 and a(n) = floor(a(n-1)^2/a(n-2))+1 for odd n (the entry
writes even twice; the name and his PARI program give odd for the second), and the rule of his PARI
program; they are used below with the quotients taken in ℚ. In the name, n is even exactly when the new
index n+2 is even.
-/

namespace OMA.S_oeis_a022030

/-- A022030: a(0) = 4, a(1) = 16; for even n, a(n+2) = ceiling(a(n+1)^2/a(n)) - 1, for odd n,
a(n+2) = floor(a(n+1)^2/a(n)) + 1. -/
def a : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | (n + 2) => if n % 2 = 0 then ⌈((a (n + 1) : ℚ) ^ 2 / (a n : ℚ))⌉ - 1
      else ⌊((a (n + 1) : ℚ) ^ 2 / (a n : ℚ))⌋ + 1

/-- The original definition: t(0) = 4, t(1) = 16, t(n+2) = ceiling(t(n+1)^2/t(n)) - 1, the greatest
integer k with k/t(n+1) < t(n+1)/t(n). -/
def t : ℕ → ℤ
  | 0 => 4
  | 1 => 16
  | (n + 2) => ⌈((t (n + 1) : ℚ) ^ 2 / (t n : ℚ))⌉ - 1

/-- Colin Barker's conjectures a(n) = 4a(n-1) - a(n-3) + a(n-4) for n ≥ 4 and g.f.
(4-x^2+x^3)/(1-4x+x^3-x^4), and M. F. Hasler's conjectured g.f. (4-x^2)/(1-4x+x^3) for the
sequence of the original definition. -/
theorem main : (∀ n : ℕ, 4 ≤ n → a n = 4 * a (n - 1) - a (n - 3) + a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
        (1 - 4 * PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4) =
      4 - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 ∧
    PowerSeries.mk (fun n => (t n : ℚ)) * (1 - 4 * PowerSeries.X + PowerSeries.X ^ 3) =
      4 - PowerSeries.X ^ 2 := by
  sorry

end OMA.S_oeis_a022030
