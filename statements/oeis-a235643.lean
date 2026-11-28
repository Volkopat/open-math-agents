import Mathlib

/-!
# A235643: Total number of sides of a tetraflake-like fractal after n iterations, a(1) = 16 (see comments).

Source: https://oeis.org/A235643
Credit: @agchua

Colin Barker (Apr 21 2014), in the formula section of A235643:
  Conjecture from Colin Barker, Apr 21 2014: (Start)
  a(n) = sqrt(2)*((3-sqrt(2))^n*(-1+sqrt(2))+(1+sqrt(2))*(3+sqrt(2))^n).
  a(n) = 6*a(n-1)-7*a(n-2).
  G.f.: 4*x*(-7*x+4) / (7*x^2-6*x+1). (End)
Definition: the sequence is the one computed by the Small Basic program of the entry, which
sets a[0] = 10, a[1] = 16 and, for n = 2, 3, ..., a[n] = t1 + t2 + t3 with t1 = 3*a[n-1],
t2 = 2*a[n-2] and t3 = Sum_{i=3..n} 2*3^(n-i+1)*a[i-3] (t3 = 0 for n = 2), and prints
a[1], a[2], ...; a[0] = 10 is an auxiliary start value, not a term (the offset is 1). These
rules determine the sequence, so the statement is made for every a : ℕ → ℕ that satisfies
them. The closed form is stated for n >= 1 (the offset), the recurrence for n >= 3 (so that
a(n-2) is a term; at n = 2 it would use the auxiliary a[0]), and the g.f. of the terms,
Sum_{n>=1} a(n) x^n, as an identity of formal power series over ℚ:
(Sum_{n>=1} a(n) X^n) * (7 X^2 - 6 X + 1) = 4 X (-7 X + 4).
-/

namespace OMA.S_oeis_a235643

/-- Barker's conjectures for the sequence of the entry's program: the closed form for n >= 1,
the recurrence a(n) = 6a(n-1) - 7a(n-2) for n >= 3, and the g.f. 4x(-7x+4)/(7x^2-6x+1). -/
theorem main : ∀ a : ℕ → ℕ, a 0 = 10 → a 1 = 16 →
    (∀ n : ℕ, 2 ≤ n → a n = 3 * a (n - 1) + 2 * a (n - 2) +
      ∑ i ∈ Finset.Icc 3 n, 2 * 3 ^ (n - i + 1) * a (i - 3)) →
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = Real.sqrt 2 * ((3 - Real.sqrt 2) ^ n * (-1 + Real.sqrt 2) +
      (1 + Real.sqrt 2) * (3 + Real.sqrt 2) ^ n)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 7 * (a (n - 2) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (7 * PowerSeries.X ^ 2 - 6 * PowerSeries.X + 1) =
      4 * PowerSeries.X * (-7 * PowerSeries.X + 4) := by
  sorry

end OMA.S_oeis_a235643
