import Mathlib

/-!
# OEIS A308109: Barker's conjectures for the sum of the middle sides of the scalene triangles

Source: https://oeis.org/A308109 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A308109 (Wesley Ivan Hurt, May 13 2019), offset 1: Take all the integer-sided triangles
with perimeter n and sides a, b, and c such that a < b < c. a(n) is the sum of all the b's.
Formula section:
a(n) = Sum_{k=1..floor((n-1)/3)} Sum_{i=k+1..floor((n-k-1)/2)} sign(floor((i+k)/(n-i-k+1))) * i.
Conjectures from Colin Barker, May 13 2019:
G.f.: x^9*(3 + 3*x + 4*x^2 + 2*x^3 + x^4) / ((1 - x)^4*(1 + x)^3*(1 + x^2)^2*(1 + x + x^2)^2).
a(n) = -a(n-1) + 2*a(n-3) + 4*a(n-4) + 2*a(n-5) - a(n-6) - 5*a(n-7) - 5*a(n-8) - a(n-9) +
2*a(n-10) + 4*a(n-11) + 2*a(n-12) - a(n-14) - a(n-15) for n>15.

Formalization notes:
* The definition follows the entry's formula line: the triangles are k < i < n - k - i, the
  factor sign(floor((i+k)/(n-i-k+1))) is 1 exactly when k + i > n - k - i (the triangle
  inequality) and 0 otherwise, and i is the middle side b. The floor of the quotient of two
  natural numbers is natural-number division (the denominator n - i - k + 1 is at least 1 in the
  range of summation), and sign is Int.sign.
* The formula gives a(0) = 0 (empty sum), so A(x) = Sum_{n >= 0} a(n) x^n is the entry's
  generating function Sum_{n >= 1} a(n) x^n; it is stated as A * D = N in the formal power series
  ring over the integers, which is equivalent because D has constant term 1. The recurrence is
  stated in the integers.
* Controls from the entry, proved in the proof file: a(1..24) = 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 4,
  4, 9, 5, 16, 11, 24, 19, 34, 28, 52, 39, 66, 59.
-/

namespace OMA.S_oeis_a308109

open PowerSeries

/-- A308109(n), by the entry's formula (the empty sum gives a(0) = 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 ((n - 1) / 3), ∑ i ∈ Finset.Icc (k + 1) ((n - k - 1) / 2),
    Int.sign (((i + k) / (n - i - k + 1) : ℕ) : ℤ) * (i : ℤ)

/-- Barker's generating function and recurrence. -/
theorem main :
    mk a * ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      X ^ 9 * (3 + 3 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4) ∧
    (∀ n : ℕ, 15 < n → a n = -a (n - 1) + 2 * a (n - 3) + 4 * a (n - 4) + 2 * a (n - 5) -
      a (n - 6) - 5 * a (n - 7) - 5 * a (n - 8) - a (n - 9) + 2 * a (n - 10) + 4 * a (n - 11) +
      2 * a (n - 12) - a (n - 14) - a (n - 15)) := by
  sorry

end OMA.S_oeis_a308109
