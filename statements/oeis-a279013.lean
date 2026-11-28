import Mathlib

/-!
# A279013: Mathar's recurrence

Source: https://oeis.org/A279013
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A279013 (offset 0): a(n) = Sum_{k=0..n} binomial(2*k,k)/(k+1)*binomial(2*n-1,n-k);
data 1, 2, 8, 35, 161, 768, 3773, 19006, 97840, 513264, 2737121, 14805805, ...

Conjecture (R. J. Mathar, Jan 27 2020): D-finite with recurrence
2*n*(n+1)*(2*n-3)*a(n) -n*(101*n^2-312*n+203)*a(n-1) +(995*n^3-5570*n^2+9567*n-4984)*a(n-2)
+2*(-2393*n^3+19300*n^2-50494*n+42835)*a(n-3) +4*(2*n7)*(1408*n^2-9889*n+16690)*a(n-4)
-2600*(n-5)*(2*n-7)*(2*n-9)*a(n-5) = 0
(the entry prints the factor (2*n-7) of the a(n-4) term as (2*n7); it is read here as (2*n-7); with
this reading the recurrence holds on the data).

Formalization: The entry gives the g.f. (2*(1-sqrt(1-((1-sqrt(1-4*x))^2)/x))*(1/sqrt(1-4*x)+1)/2*x)/((1-sqrt(1-4*x))^2), and
this closed form is used as the definition here. T is the formal power series over ℚ with T^2 = 1-4*x
and constant term 1; U is the formal power series with x*U^2 = x - (1-T)^2 and constant term 1, that is
U = sqrt(1 - (1 - sqrt(1-4x))^2/x) (the constant terms select the branches of the square roots); and G is
determined by G*(1-T)^2*T = x*(1-U)*(1+T), the closed form multiplied by (1-T)^2*T (its constant term 1
is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (420)*(768) + (-5840)*(161) + (27976)*(35) + (-52520)*(8) + (29340)*(2) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a279013

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A279013, for n ≥ 5. -/
theorem main : ∀ T U G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    X * U ^ 2 = X - (1 - T) ^ 2 →
    coeff 0 U = 1 →
    G * ((1 - T) ^ 2 * T) = X * (1 - U) * (1 + T) →
    coeff 0 G = 1 →
    ∀ n : ℕ, 5 ≤ n →
      (-6 * (n : ℚ) - 2 * (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 3) * coeff n G + (-203 * (n : ℚ) + 312 * (n : ℚ) ^ 2 - 101 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-4984 + 9567 * (n : ℚ) - 5570 * (n : ℚ) ^ 2 + 995 * (n : ℚ) ^ 3) * coeff (n - 2) G + (85670 - 100988 * (n : ℚ) + 38600 * (n : ℚ) ^ 2 - 4786 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-467320 + 410412 * (n : ℚ) - 118536 * (n : ℚ) ^ 2 + 11264 * (n : ℚ) ^ 3) * coeff (n - 4) G + (819000 - 579800 * (n : ℚ) + 135200 * (n : ℚ) ^ 2 - 10400 * (n : ℚ) ^ 3) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a279013
