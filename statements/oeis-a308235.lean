import Mathlib

/-!
# OEIS A308235: Barker's conjectures for the total surface area of the prisms on the sides of the scalene triangles

Source: https://oeis.org/A308235 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A308235 (Wesley Ivan Hurt, May 16 2019), offset 1: Take apart the sides of each of the
integer-sided scalene triangles with perimeter n (at their vertices) and rearrange them orthogonally
in 3-space so that their endpoints coincide at a single point. a(n) is the total surface area of all
rectangular prisms enclosed in this way.
Formula section:
a(n) = 2 * Sum_{k=1..floor((n-1)/3)} Sum_{i=k+1..floor((n-k-1)/2)} sign(floor((i+k)/(n-i-k+1))) *
(i*k + i*(n-i-k) + k*(n-i-k)).
Conjectures from Colin Barker, May 16 2019:
G.f.: 2*x^9*(26 + 52*x + 90*x^2 + 97*x^3 + 94*x^4 + 71*x^5 + 56*x^6 + 31*x^7 + 17*x^8 + 5*x^9 +
x^10) / ((1 - x)^5*(1 + x)^4*(1 + x^2)^3*(1 + x + x^2)^3).
a(n) = -2*a(n-1) - 2*a(n-2) + a(n-3) + 7*a(n-4) + 10*a(n-5) + 7*a(n-6) - 5*a(n-7) - 17*a(n-8) -
19*a(n-9) - 9*a(n-10) + 9*a(n-11) + 19*a(n-12) + 17*a(n-13) + 5*a(n-14) - 7*a(n-15) - 10*a(n-16) -
7*a(n-17) - a(n-18) + 2*a(n-19) + 2*a(n-20) + a(n-21) for n>21.

Formalization notes:
* The definition follows the entry's formula line: the triangles are k < i < n - k - i, the factor
  sign(floor((i+k)/(n-i-k+1))) is 1 exactly when k + i > n - k - i (the triangle inequality) and 0
  otherwise, and i*k + i*(n-i-k) + k*(n-i-k) is half the surface area of the box with edges k, i and
  n - k - i (the natural-number subtraction is exact in the range of summation). The floor of the
  quotient of two natural numbers is natural-number division (the denominator n - i - k + 1 is at
  least 1 in the range of summation), and sign is Int.sign.
* The formula gives a(0) = 0 (empty sum), so A(x) = Sum_{n >= 0} a(n) x^n is the entry's
  generating function Sum_{n >= 1} a(n) x^n; it is stated as A * D = N in the formal power series
  ring over the integers, which is equivalent because D has constant term 1. The recurrence is
  stated in the integers.
* Controls from the entry, proved in the proof file: a(1..24) = 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 76,
  94, 212, 126, 426, 328, 724, 624, 1130, 1020, 1938, 1540, 2648, 2568.
-/

namespace OMA.S_oeis_a308235

open PowerSeries

/-- A308235(n), by the entry's formula (the empty sum gives a(0) = 0). -/
def a (n : ℕ) : ℤ :=
  2 * ∑ k ∈ Finset.Icc 1 ((n - 1) / 3), ∑ i ∈ Finset.Icc (k + 1) ((n - k - 1) / 2),
    Int.sign (((i + k) / (n - i - k + 1) : ℕ) : ℤ) * ((i * k + i * (n - i - k) + k * (n - i - k) : ℕ) : ℤ)

/-- Barker's generating function and recurrence. -/
theorem main :
    mk a * ((1 - X) ^ 5 * (1 + X) ^ 4 * (1 + X ^ 2) ^ 3 * (1 + X + X ^ 2) ^ 3) =
      2 * X ^ 9 * (26 + 52 * X + 90 * X ^ 2 + 97 * X ^ 3 + 94 * X ^ 4 + 71 * X ^ 5 + 56 * X ^ 6 +
        31 * X ^ 7 + 17 * X ^ 8 + 5 * X ^ 9 + X ^ 10) ∧
    (∀ n : ℕ, 21 < n → a n = -2 * a (n - 1) - 2 * a (n - 2) + a (n - 3) + 7 * a (n - 4) + 10 * a (n - 5)
      + 7 * a (n - 6) - 5 * a (n - 7) - 17 * a (n - 8) - 19 * a (n - 9)
      - 9 * a (n - 10) + 9 * a (n - 11) + 19 * a (n - 12) + 17 * a (n - 13)
      + 5 * a (n - 14) - 7 * a (n - 15) - 10 * a (n - 16) - 7 * a (n - 17)
      - a (n - 18) + 2 * a (n - 19) + 2 * a (n - 20) + a (n - 21)) := by
  sorry

end OMA.S_oeis_a308235
