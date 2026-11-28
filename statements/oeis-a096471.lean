import Mathlib

/-!
# A096471: Mathar's recurrence

Source: https://oeis.org/A096471
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A096471 (offset 2): number of degree-n permutations with exactly one even cycle;
data 1, 3, 12, 60, 345, 2415, 18480, 166320, 1596105, 17557155, 202951980, 2638375740, ...

Conjecture (R. J. Mathar, Jul 06 2023): D-finite with recurrence
a(n) -3*a(n-1) +(-2*n^2+8*n-3)*a(n-2) +(n-2)*(4*n-15)*a(n-3) +(n-3)*(n^3-9*n^2+22*n-7)*a(n-4)
-(n-3)*(n-4)*(n-5)^2*a(n-5) = 0.

Formalization: the entry gives the e.g.f. -1/2*((1+x)/(1-x))^(1/2)*log(1-x^2), and this is used as the definition
here. S is the formal power series over ℚ with S^2*(1-x) = 1+x and constant term 1, that is
S = ((1+x)/(1-x))^(1/2) (the constant term selects the branch of the square root); L is the formal
power series with zero constant term and (1-x^2)*L' = -2*x, that is L = log(1-x^2) (these two
conditions determine L); and the e.g.f. G is determined by 2*G = -S*L;
a(n) = n! [x^n] G, which is 0 for n < 2. The sequence has offset 2 and the recurrence involves a(n-5), so
every index is at least the offset for n ≥ 7. `main` is stated for n ≥ 5, with a(0) = a(1) = 0 as given
by the e.g.f.; this includes every n ≥ 7. It is checked by the data, for example at n = 5: (1)*(60) + (-3)*(12) + (-13)*(3) + (15)*(1) + (6)*(0) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a096471

open PowerSeries

/-- The sequence with exponential generating function G: a(n) = n! [x^n] G. -/
noncomputable def a (G : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n G

/-- Mathar's conjectured recurrence for A096471 (a(n) = n! [x^n] G), for n ≥ 5. -/
theorem main : ∀ S L G : ℚ⟦X⟧, S ^ 2 * (1 - X) = 1 + X →
    coeff 0 S = 1 →
    coeff 0 L = 0 →
    (1 - X ^ 2) * derivative ℚ L = -(2 * X) →
    2 * G = -(S * L) →
    ∀ n : ℕ, 5 ≤ n →
      (1) * a G n + (-3) * a G (n - 1) +
        (-3 + 8 * (n : ℚ) - 2 * (n : ℚ) ^ 2) * a G (n - 2) + (30 - 23 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * a G (n - 3) +
        (21 - 73 * (n : ℚ) + 49 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3 + (n : ℚ) ^ 4) * a G (n - 4) + (-300 + 295 * (n : ℚ) - 107 * (n : ℚ) ^ 2 + 17 * (n : ℚ) ^ 3 - (n : ℚ) ^ 4) * a G (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a096471
