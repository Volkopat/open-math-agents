import Mathlib

/-!
# Floors of harmonic means of successive cubic intervals

Clark Kimberling defines a(n) for n ≥ 1 using all integers strictly after
g(n−1) and at most g(n). The harmonic mean is rational, so its floor can
be taken exactly. The zero coefficient is padding for the two generating
functions. The recurrence is asserted at each index in the specified range
where its seven predecessors are terms of the sequence.

The power of −1 in Ramaharo's expression has exponent (n−1)!. Natural
subtraction in its floor term implements max(0,n−4).

Source: https://oeis.org/A227015
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a227015

def g (n : ℕ) : ℕ := n^3 + n^2 + n + 1

def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    let first := g (n-1) + 1
    let count := g n - g (n-1)
    let reciprocals := (List.range count).map fun j => (1 : ℚ) / (first + j : ℕ)
    ⌊(count : ℚ) / reciprocals.sum⌋

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 < n → 7 < n → a n = 3*a (n-1) - 3*a (n-2) + a (n-3) +
      a (n-4) - 3*a (n-5) + 3*a (n-6) - a (n-7)) ∧
    (PowerSeries.mk a * ((X-1)^4 * (1 + X + X^2 + X^3)) =
      X * (2 + 2*X + 8*X^2 + 4*X^3 + 5*X^4 + 4*X^5 - 2*X^6 +
        3*X^7 - 3*X^8 + X^9)) ∧
    (∀ n : ℕ, 0 < n → 2*a n = (-1 : ℤ)^((n-1).factorial) +
      2*(n : ℤ)^3 - (n : ℤ)^2 + (n : ℤ) + 3 + 2*(((n-4)/4 : ℕ) : ℤ)) ∧
    (∀ x : ℝ, HasSum (fun n : ℕ => (a n : ℝ) * x^n / n.factorial)
      (Real.exp (-x) / 24 *
        (Real.exp x * (6*Real.sin x + 6*Real.cos x + 4*x^3 - 24) +
         Real.exp (2*x) * (24*x^3 + 60*x^2 + 30*x + 15) + 3))) := by
  sorry

end OMA.S_oeis_a227015
