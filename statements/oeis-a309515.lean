import Mathlib

/-!
# A309515: Sum of the even parts of the partitions of n into 3 parts.

Source: https://oeis.org/A309515
Credit: @Harsha0912

Conjectures (Colin Barker, Aug 06 2019, in A309515), both stated:
G.f.: 2*x^4*(1 + x + 5*x^2 + 9*x^4 + 9*x^6 + 7*x^8 + 4*x^10 - x^11 + x^12) /
((1 - x)^4*(1 + x)^3*(1 - x + x^2)^2*(1 + x^2)^2*(1 + x + x^2)^2).
a(n) = a(n-1) - a(n-2) + a(n-3) + a(n-4) - a(n-5) + 3*a(n-6) - 3*a(n-7) + 2*a(n-8) - 2*a(n-9)
- 2*a(n-10) + 2*a(n-11) - 3*a(n-12) + 3*a(n-13) - a(n-14) + a(n-15) + a(n-16) - a(n-17)
+ a(n-18) - a(n-19) for n > 18.

Conventions:
* Offset 0. A partition of n into 3 parts is j <= i <= n - i - j with
  1 <= j <= floor(n/3) and j <= i <= floor((n-j)/2). This is the OEIS formula
  a(n) = Sum_{j=1..floor(n/3)} Sum_{i=j..floor((n-j)/2)}
           (i * ((i-1) mod 2) + j * ((j-1) mod 2) + (n-i-j) * ((n-i-j-1) mod 2)),
  where for a positive part m, m * ((m-1) mod 2) is m if m is even and 0 if m is odd.
  All three parts are positive in the range of summation.
* The g.f. is stated over the rationals, cleared of its denominator: the power series with
  coefficients a(n) (n >= 0) times the denominator equals the numerator.
* The recurrence is stated in the integers.
-/

namespace OMA.S_oeis_a309515

open PowerSeries

/-- A part `m` contributes `m` if it is even and `0` otherwise. -/
def evenPart (m : ℕ) : ℕ := if Even m then m else 0

/-- A309515: the sum of the even parts over all partitions `j <= i <= n - i - j` of `n`
into 3 parts. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 (n / 3), ∑ i ∈ Finset.Icc j ((n - j) / 2),
    (evenPart i + evenPart j + evenPart (n - i - j))

/-- Barker's conjectures for A309515: the generating function, and the linear recurrence for
`n > 18`. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 - X + X ^ 2) ^ 2 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      2 * X ^ 4 * (1 + X + 5 * X ^ 2 + 9 * X ^ 4 + 9 * X ^ 6 + 7 * X ^ 8 + 4 * X ^ 10 - X ^ 11
        + X ^ 12)) ∧
    (∀ n : ℕ, 18 < n →
      (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 4) - a (n - 5) + 3 * a (n - 6)
        - 3 * a (n - 7) + 2 * a (n - 8) - 2 * a (n - 9) - 2 * a (n - 10) + 2 * a (n - 11)
        - 3 * a (n - 12) + 3 * a (n - 13) - a (n - 14) + a (n - 15) + a (n - 16) - a (n - 17)
        + a (n - 18) - a (n - 19)) := by
  sorry

end OMA.S_oeis_a309515
