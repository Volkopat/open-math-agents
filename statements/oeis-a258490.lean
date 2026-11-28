import Mathlib

/-!
# A258490: Mathar's recurrence

Source: https://oeis.org/A258490
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Aug 07 2015); the entry records it as a conjecture and notes no proof or
verification of it.

A258490 (offset 3): number of words of length 2n such that all letters of the ternary alphabet occur at least
once and are introduced in ascending order and which can be built by repeatedly inserting doublets into the
initially empty word;
data 5, 56, 465, 3509, 25571, 184232, 1325609, 9567545, 69387483, 505915981, ...

Conjecture (R. J. Mathar, Aug 07 2015):
4*n*(n-1)*(46829*n-161203)*a(n) -(n-1)*(4865671*n^2-22433759*n+19821114)*a(n-1)
+6*(7756949*n^3-53792553*n^2+117956226*n-84118712)*a(n-2)
+(-200071007*n^3+1677158106*n^2-4623144589*n+4201946850)*a(n-3)
+2*(2*n-7)*(93171685*n^2-585009841*n+881711802)*a(n-4) -72*(2*n-7)*(2*n-9)*(744719*n-1901876)*a(n-5) = 0.

Formalization: the entry gives the g.f. (1/6) * (B(x) - 3*C(x) + 3/(1-x) - 1), where B(x) and C(x) are the g.f.s
of A089022 and A000984 respectively (John Tyler Rascoe, Nov 25 2025); A089022 records the g.f.
B(x) = 4/(1+3*sqrt(1-8*x)), and C(x) = 1/sqrt(1-4*x) is the g.f. of the central binomial coefficients A000984.
This closed form is used as the definition here. T and W are the formal power series over ℚ with
T^2 = 1-8*x, W^2 = 1-4*x and constant terms 1 (the constant terms select the branches of the square roots),
so that B = 4/(1 + 3*T) and C = 1/W; and G is determined by
6*(1 + 3*T)*W*(1 - x)*G = 4*W*(1 - x) - 3*(1 + 3*T)*(1 - x) + 3*(1 + 3*T)*W - (1 + 3*T)*W*(1 - x),
the stated expression multiplied by the common denominator 6*(1 + 3*T)*W*(1 - x), a power series with
constant term 24 (so this equation has exactly one solution G); a(n) = [x^n] G. The sequence has offset 3
and the recurrence involves a(n-5), so it is stated for n ≥ 8, where every index is at least the offset; it
is checked by the data, for example at n = 8:
(47808096)*(184232) + (-1062277902)*(25571) + (8330193552)*(3509) + (-27881446662)*(465) + (38963176452)*(56) + (-18397453536)*(5) = 0.
-/

namespace OMA.S_oeis_a258490

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A258490, for n ≥ 8. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 8 * X →
    coeff 0 T = 1 →
    W ^ 2 = 1 - 4 * X →
    coeff 0 W = 1 →
    6 * (1 + 3 * T) * W * (1 - X) * G =
      4 * W * (1 - X) - 3 * (1 + 3 * T) * (1 - X) + 3 * (1 + 3 * T) * W - (1 + 3 * T) * W * (1 - X) →
    ∀ n : ℕ, 8 ≤ n →
      (644812 * (n : ℚ) - 832128 * (n : ℚ) ^ 2 + 187316 * (n : ℚ) ^ 3) * coeff n G + (19821114 - 42254873 * (n : ℚ) + 27299430 * (n : ℚ) ^ 2 - 4865671 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-504712272 + 707737356 * (n : ℚ) - 322755318 * (n : ℚ) ^ 2 + 46541694 * (n : ℚ) ^ 3) * coeff (n - 2) G + (4201946850 - 4623144589 * (n : ℚ) + 1677158106 * (n : ℚ) ^ 2 - 200071007 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-12343965228 + 11716984982 * (n : ℚ) - 3644442954 * (n : ℚ) ^ 2 + 372686740 * (n : ℚ) ^ 3) * coeff (n - 4) G + (8626909536 - 7759967688 * (n : ℚ) + 2263572864 * (n : ℚ) ^ 2 - 214479072 * (n : ℚ) ^ 3) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a258490
