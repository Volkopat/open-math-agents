import Mathlib

/-!
# OEIS A294513: Lang's conjecture a(n) = 2*A250327(n+1)/(n+1)

Source: https://oeis.org/A294513 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

A294513(n), n >= 0, is the denominator of V(3,2;n) = Sum_{k=0..n} 1/((k+1)*(3*k+2)), the partial
sums of the reciprocals of twice the pentagonal numbers. A250327(m), m >= 1, is the numerator of
the harmonic mean of the first m pentagonal numbers k*(3*k-1)/2. The formula section of A294513
states (Wolfdieter Lang, 2017): a(n) = 2*A250327(n+1)/(n+1) [conjecture].

Formalization notes:
* The identity is stated in the rationals, so no integer division is involved.
* The harmonic mean of x_1, ..., x_m is m / (1/x_1 + ... + 1/x_m).
* Controls from the entries: A294513 begins 2, 5, 120, 1320 and A250327 begins 1, 5, 180, 2640;
  the definitions below give V 2 = 77/120 and the harmonic mean 180/77 for m = 3.
-/

namespace OMA.S_oeis_a294513

/-- V(3,2;n) = Sum_{k=0..n} 1/((k+1)(3k+2)). -/
def V (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / ((k + 1) * (3 * k + 2))

/-- A294513(n): the denominator of V(3,2;n). -/
def a (n : ℕ) : ℕ := (V n).den

/-- A250327(m): the numerator of the harmonic mean of the first m pentagonal numbers. -/
def b (m : ℕ) : ℤ :=
  ((m : ℚ) / ∑ k ∈ Finset.Icc 1 m, (1 : ℚ) / ((k : ℚ) * (3 * k - 1) / 2)).num

/-- Lang's conjecture: a(n) = 2*A250327(n+1)/(n+1) for every n >= 0. -/
theorem main : ∀ n : ℕ, (a n : ℚ) = 2 * (b (n + 1) : ℚ) / ((n : ℚ) + 1) := by
  sorry

end OMA.S_oeis_a294513
