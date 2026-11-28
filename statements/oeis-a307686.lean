import Mathlib

/-!
# A307686: Sum of the smallest side lengths of all integer-sided triangles with perimeter n.

Source: https://oeis.org/A307686
Credit: @Harsha0912

Conjecture (Colin Barker, May 12 2019, in A307686):
a(n) = -a(n-1) + 2*a(n-3) + 4*a(n-4) + 2*a(n-5) - a(n-6) - 5*a(n-7) - 5*a(n-8) - a(n-9)
+ 2*a(n-10) + 4*a(n-11) + 2*a(n-12) - a(n-14) - a(n-15) for n > 15.

Conventions:
* Offset 1. A triangle with perimeter n has integer sides k <= i <= c with c = n - i - k,
  so 1 <= k <= floor(n/3) and k <= i <= floor((n-k)/2); it is a (nondegenerate) triangle iff
  i + k > c. This is the OEIS formula
  a(n) = Sum_{k=1..floor(n/3)} Sum_{i=k..floor((n-k)/2)} sign(floor((i+k)/(n-i-k+1))) * k,
  since sign(floor((i+k)/(n-i-k+1))) = 1 exactly when i + k > n - i - k, and 0 otherwise.
* The recurrence is stated in the integers.
* Barker's conjectured g.f. x^3*(1 + x + x^2 + x^3 + x^4 + x^5 + x^6) /
  ((1 - x)^4*(1 + x)^3*(1 + x^2)^2*(1 + x + x^2)^2) is the ordinary generating function
  Sum_{n >= 1} a(n) x^n (here `a 0 = 0`); it is stated over the rationals with the denominator
  multiplied out.
-/

namespace OMA.S_oeis_a307686

open PowerSeries

/-- A307686: the sum of the smallest sides `k` over all integer triangles `k <= i <= n - i - k`
with perimeter `n`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (n / 3),
    ∑ i ∈ (Finset.Icc k ((n - k) / 2)).filter (fun i => n - i - k < i + k), k

/-- Barker's conjectures for A307686: the generating function, and the linear recurrence for
`n > 15`. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      X ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6)) ∧
    (∀ n : ℕ, 15 < n →
      (a n : ℤ) = -(a (n - 1) : ℤ) + 2 * a (n - 3) + 4 * a (n - 4) + 2 * a (n - 5) - a (n - 6)
        - 5 * a (n - 7) - 5 * a (n - 8) - a (n - 9) + 2 * a (n - 10) + 4 * a (n - 11)
        + 2 * a (n - 12) - a (n - 14) - a (n - 15)) := by
  sorry

end OMA.S_oeis_a307686
