import Mathlib

/-!
# A235089: a(n)*Pi is the total length of irregular spiral (center points: 2, 1, 3, 4) after n rotations.

Source: https://oeis.org/A235089
Credit: @agchua

The claims of the entry, as quoted by the problem:
  Conjecture: Numbers equivalent 0 or 3 modulo 10. - Ralf Stephan, Jan 13 2014
  Conjectures from Colin Barker, Jan 16 2014: (Start)
  a(n) = -1+(-1)^n+5*n.
  a(n) = a(n-1)+a(n-2)-a(n-3).
  G.f.: x*(7*x+3) / ((x-1)^2*(x+1)). (End)
  a(n) = 5*n - 2*floor((n+1)/2) + 2*floor(n/2). In particular, Barker's conjectures are true (see
  Fried link). - Sela Fried, May 08 2026
The entry already says that Barker's conjectures are true (Sela Fried). This file states all five
claims, with offset 1: the terms are exactly the positive numbers that are 0 or 3 modulo 10, listed in
increasing order; the closed form and Fried's formula for n ≥ 1; the recurrence for n ≥ 4, where all
its indices are terms; the g.f. as an identity of formal power series over ℚ for the series of a(n) x^n
over n ≥ 1: (∑_{n ≥ 1} a(n) X^n) * ((X - 1)^2 * (X + 1)) = X * (7X + 3).
Definition: the entry's Small Basic program, a(1) = 3 and a(n+1) = a(n) + 7 if n + 1 is even,
a(n+1) = a(n) + 3 otherwise (the lengths added by the half circles of the construction in the
comment). a(0) is not a term; the definition below sets it to 0.
-/

namespace OMA.S_oeis_a235089

/-- A235089: a(1) = 3, a(n+1) = a(n) + (7 if n + 1 is even, else 3); a(0) = 0 is not a term. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | (n + 2) => a (n + 1) + (if (n + 2) % 2 = 0 then 7 else 3)

/-- Stephan's conjecture (the terms, in increasing order, are the positive numbers that are 0 or 3
modulo 10), Barker's three conjectures, and Fried's formula. -/
theorem main :
    ((∀ n : ℕ, 1 ≤ n → a n < a (n + 1)) ∧
      ∀ k : ℕ, (∃ n : ℕ, 1 ≤ n ∧ a n = k) ↔ (0 < k ∧ (k % 10 = 0 ∨ k % 10 = 3))) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = -1 + (-1) ^ n + 5 * n) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((PowerSeries.X - 1) ^ 2 * (PowerSeries.X + 1)) =
      PowerSeries.X * (7 * PowerSeries.X + 3) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 5 * n - 2 * (((n + 1) / 2 : ℕ) : ℤ) + 2 * ((n / 2 : ℕ) : ℤ)) := by
  sorry

end OMA.S_oeis_a235089
