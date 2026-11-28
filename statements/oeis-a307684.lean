import Mathlib

/-!
# A307684: Total volume of all rectangular prisms with dimensions r X s X t where r, s and t are the smallest, middle and largest parts in each partition of n into 3 parts.

Source: https://oeis.org/A307684
Credit: @Harsha0912

Conjectures (Colin Barker, Apr 22 2019, in A307684), both stated:
G.f.: x^3*(1 + 3*x + 7*x^2 + 15*x^3 + 23*x^4 + 21*x^5 + 18*x^6 + 14*x^7 + 6*x^8) /
((1 - x)^6*(1 + x)^3*(1 + x + x^2)^4).
a(n) = -a(n-1) + 2*a(n-2) + 6*a(n-3) + 3*a(n-4) - 9*a(n-5) - 14*a(n-6) - 2*a(n-7) + 16*a(n-8)
+ 16*a(n-9) - 2*a(n-10) - 14*a(n-11) - 9*a(n-12) + 3*a(n-13) + 6*a(n-14) + 2*a(n-15) - a(n-16)
- a(n-17) for n > 17.

Conventions:
* Offset 1. A partition of n into 3 parts is k <= i <= n - i - k with 1 <= k <= floor(n/3)
  and k <= i <= floor((n-k)/2); this is the OEIS formula
  a(n) = Sum_{k=1..floor(n/3)} Sum_{i=k..floor((n-k)/2)} i * k * (n-i-k).
  The definition also gives a(0) = 0, so the power series below starts at n = 0, matching the
  g.f., whose expansion starts at x^1 with coefficient a(1) = 0.
* The g.f. is stated over the rationals, cleared of its denominator.
* The recurrence is stated in the integers.
-/

namespace OMA.S_oeis_a307684

open PowerSeries

/-- A307684: the sum of `k * i * (n - i - k)` over all partitions `k <= i <= n - i - k` of `n`
into 3 parts. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n / 3), ∑ i ∈ Finset.Icc k ((n - k) / 2), i * k * (n - i - k)

/-- Barker's conjectures for A307684: the generating function, and the linear recurrence for
`n > 17`. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 3 * (1 + X + X ^ 2) ^ 4) =
      X ^ 3 * (1 + 3 * X + 7 * X ^ 2 + 15 * X ^ 3 + 23 * X ^ 4 + 21 * X ^ 5 + 18 * X ^ 6
        + 14 * X ^ 7 + 6 * X ^ 8)) ∧
    (∀ n : ℕ, 17 < n →
      (a n : ℤ) = -(a (n - 1) : ℤ) + 2 * a (n - 2) + 6 * a (n - 3) + 3 * a (n - 4)
        - 9 * a (n - 5) - 14 * a (n - 6) - 2 * a (n - 7) + 16 * a (n - 8) + 16 * a (n - 9)
        - 2 * a (n - 10) - 14 * a (n - 11) - 9 * a (n - 12) + 3 * a (n - 13) + 6 * a (n - 14)
        + 2 * a (n - 15) - a (n - 16) - a (n - 17)) := by
  sorry

end OMA.S_oeis_a307684
