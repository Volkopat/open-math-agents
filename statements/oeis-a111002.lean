import Mathlib

/-!
# A111002: a(n) = gcd(f(n), f(n+1)) where f(n) = n^4 + n^2 + 1.

Source: https://oeis.org/A111002
Credit: @agchua

Colin Barker (Oct 06 2015), in the formula section of A111002:
  Conjectures: a(n) = 3*a(n-7) - 3*a(n-14) + a(n-21) for n>20. G.f.: ... / ((x-1)^3*(x^6+...+1)^3).
This file states the recurrence, for n > 20 exactly as written. (The g.f. conjecture has denominator
(x-1)^3 (x^6+x^5+...+1)^3 = (x^7-1)^3, so it is the same recurrence together with the listed initial
terms; it is not restated here.) The sequence has offset 0; gcd is Nat.gcd; terms are taken in ℤ.
-/

namespace OMA.S_oeis_a111002

/-- f(n) = n^4 + n^2 + 1. -/
def f (n : ℕ) : ℕ := n ^ 4 + n ^ 2 + 1

/-- A111002(n) = gcd(f(n), f(n+1)). -/
def a (n : ℕ) : ℕ := Nat.gcd (f n) (f (n + 1))

/-- Barker's conjecture: a(n) = 3a(n-7) - 3a(n-14) + a(n-21) for n > 20. -/
theorem main : ∀ n : ℕ, 20 < n →
    (a n : ℤ) = 3 * (a (n - 7) : ℤ) - 3 * (a (n - 14) : ℤ) + (a (n - 21) : ℤ) := by
  sorry

end OMA.S_oeis_a111002
