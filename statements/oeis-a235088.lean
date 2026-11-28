import Mathlib

/-!
# A235088: a(n)*Pi is the total length of irregular spiral (center points: 1, 2, 3, 4) after n rotations.

Source: https://oeis.org/A235088
Credit: @agchua

Formula section of A235088 (offset 1), verbatim:
  a(n) = 2*floor((n-1)^2/4) + 3*ceiling(n^2/2) (conjectured). - _Ralf Stephan_, Jan 13 2014
  Conjecture: a(n) = 1-(-1)^n-n+2*n^2. a(n) = 2*a(n-1)-2*a(n-3)+a(n-4). G.f.: -x*(5*x^2+3)/((x-1)^3*(x+1)). - _Colin Barker_, Jan 16 2014
  a(n) = 2*n^2 + n - 4*floor(n/2). In particular, Stephan's and Barker's conjectures are true (see Fried link). - _Sela Fried_, May 08 2026
The entry itself records (Sela Fried, 2026, with a linked proof) that these conjectures are
true. This file states all of them: Stephan's formula, Barker's closed form, his recurrence (for
n >= 5, so that every index is a term), his g.f. as an identity of formal power series over Q
(the coefficient of X^0 is a(0), which the definition below makes 0, in accordance with the
factor x of the g.f., offset 1), and Fried's formula.
Definition: the program of the entry (Small Basic), verbatim:
  a[1]=3 / d1=3 / For n = 1 To 100 / If Math.Remainder(n+3,2)=1 then / d1=d1+8 / EndIf /
  a[n+1]=a[n]+d1 / TextWindow.Write(a[n]+, ) / EndFor
(the line breaks of the program are written as /, and the quotes of the string literal, a comma
and a space, are left out; the Write line only prints). So a(1) = 3 and a(n+1) = a(n) + d(n), where
d(n) is the value of d1 after the n-th pass of the loop: d(0) = 3, and d(n) = d(n-1) + 8 when
n + 3 is odd, d(n) = d(n-1) otherwise. The definition gives the listed terms
3, 6, 17, 28, 47, 66, 93, 120, ... (all 60 listed terms checked).
-/

namespace OMA.S_oeis_a235088

/-- d n = the value of d1 after n passes of the loop (d 0 = 3 is its value before the loop). -/
def d : ℕ → ℕ
  | 0 => 3
  | (n + 1) => if (n + 1 + 3) % 2 = 1 then d n + 8 else d n

/-- A235088 (offset 1): a(1) = 3 and a(n+1) = a(n) + d(n) for n >= 1; a(0) = 0 is not a term. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | (n + 2) => a (n + 1) + d (n + 1)

/-- The conjectures of Stephan and Barker, and Fried's formula. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) = 2 * ⌊((n : ℚ) - 1) ^ 2 / 4⌋ + 3 * ⌈(n : ℚ) ^ 2 / 2⌉) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 1 - (-1) ^ n - n + 2 * n ^ 2) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((PowerSeries.X - 1) ^ 3 * (PowerSeries.X + 1)) =
      -PowerSeries.X * (5 * PowerSeries.X ^ 2 + 3) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 2 * n ^ 2 + n - 4 * ⌊(n : ℚ) / 2⌋) := by
  sorry

end OMA.S_oeis_a235088
