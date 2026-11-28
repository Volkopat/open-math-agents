import Mathlib

/-!
# A200753: Mathar's recurrence

Source: https://oeis.org/A200753
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A200753 (offset 0): g.f. satisfies: A(x) = 1 + (x-x^2)*A(x)^3;
data 1, 1, 2, 6, 22, 89, 381, 1694, 7744, 36168, 171831, 827814, ...

Conjecture (R. J. Mathar, Nov 22 2011):
2n*(2n+1)*a(n) -(13n-7)(3n-2)*a(n-1) +4(29n^2-87n+67)*a(n-2) +9(-15n^2+69n-80)*a(n-3)
+6(3n-8)(3n-10)*a(n-4) = 0.

Formalization: G is the formal power series over ℚ with G = 1 + (x - x^2)*G^3; this equation determines G, and
its constant term is 1;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (72)*(22) + (-450)*(6) + (732)*(2) + (-396)*(1) + (48)*(1) = 0.
-/

namespace OMA.S_oeis_a200753

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A200753, for n ≥ 4. -/
theorem main : ∀ G : ℚ⟦X⟧, G = 1 + (X - X ^ 2) * G ^ 3 →
    ∀ n : ℕ, 4 ≤ n →
      (2 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff n G + (-14 + 47 * (n : ℚ) - 39 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (268 - 348 * (n : ℚ) + 116 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-720 + 621 * (n : ℚ) - 135 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (480 - 324 * (n : ℚ) + 54 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a200753
