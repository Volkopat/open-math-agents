import Mathlib

/-!
# A243642: Mathar's recurrence, corrected to n ≥ 7

Source: https://oeis.org/A243642
Credit: @ivillar

Status: false as stated at n = 6 (the left side is 24 at n = 6 on the OEIS data); `main` is the
corrected recurrence (n ≥ 7), which is proved.

A243642 (offset 0): expansion of -(4*x)/((1-sqrt(1-4*x))/2-sqrt(-3*(1-sqrt(1-4*x))+(1-sqrt(1-4*x))^2/4+1)+1);
data -1, 2, 3, 10, 43, 210, 1106, 6120, 35059, 206050, 1235130, 7520860, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
+16*n*(n-1)*(n-2)*a(n) -4*(n-1)*(n-2)*(43*n-54)*a(n-1) +2*(n-2)*(52*n^2+695*n-2439)*a(n-2)
+(3479*n^3-42714*n^2+169789*n-219234)*a(n-3) +2*(-4633*n^3+64020*n^2-293825*n+447594)*a(n-4)
+4*(2*n-11)*(296*n^2-3643*n+11187)*a(n-5) +24*(n-7)*(2*n-11)*(2*n-13)*a(n-6) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-4*x and constant term 1; V is the formal power
series with 4*V^2 = -12*(1-T) + (1-T)^2 + 4 and constant term 1, that is
V = sqrt(-3*(1-T) + (1-T)^2/4 + 1) (the constant terms select the branches of the square roots); and G
is determined by G*((1-T) - 2*V + 2) = -8*x, which is the stated expression with numerator and
denominator multiplied by 2 (its constant term is recorded as a hypothesis);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 7): on the data the left side of the recurrence as
stated is 24 at n = 6, and it vanishes from n = 7 on.
-/

namespace OMA.S_oeis_a243642

open PowerSeries

/-- The corrected recurrence (n ≥ 7): Mathar's recurrence, which fails at n = 6. -/
theorem main : ∀ T V G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    4 * V ^ 2 = -12 * (1 - T) + (1 - T) ^ 2 + 4 →
    coeff 0 V = 1 →
    G * ((1 - T) - 2 * V + 2) = -(8 * X) →
    coeff 0 G = -1 →
    ∀ n : ℕ, 7 ≤ n →
      (32 * (n : ℚ) - 48 * (n : ℚ) ^ 2 + 16 * (n : ℚ) ^ 3) * coeff n G + (432 - 992 * (n : ℚ) + 732 * (n : ℚ) ^ 2 - 172 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (9756 - 7658 * (n : ℚ) + 1182 * (n : ℚ) ^ 2 + 104 * (n : ℚ) ^ 3) * coeff (n - 2) G + (-219234 + 169789 * (n : ℚ) - 42714 * (n : ℚ) ^ 2 + 3479 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (895188 - 587650 * (n : ℚ) + 128040 * (n : ℚ) ^ 2 - 9266 * (n : ℚ) ^ 3) * coeff (n - 4) G + (-492228 + 249788 * (n : ℚ) - 42168 * (n : ℚ) ^ 2 + 2368 * (n : ℚ) ^ 3) * coeff (n - 5) G +
        (-24024 + 11496 * (n : ℚ) - 1824 * (n : ℚ) ^ 2 + 96 * (n : ℚ) ^ 3) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a243642
