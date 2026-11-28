import Mathlib

/-!
# A032123: Mathar's recurrence

Source: https://oeis.org/A032123
Credit: @ivillar

Status: known result. The links of the entry record a proof: Tong Niu, A short proof of Mathar's 2013
recurrence conjecture for the reversible-binary-string sequence A032123, arXiv:2605.14213, 2026.

A032123 (offset 0): number of 2n-bead black-white reversible strings with n black beads;
data 1, 1, 4, 10, 38, 126, 472, 1716, 6470, 24310, 92504, 352716, ...

Conjecture (R. J. Mathar, Nov 09 2013): D-finite with recurrence
n*(n-1)*a(n) -2*(n-1)*(3*n-4)*a(n-1) +4*(2*n^2-14*n+19)*a(n-2)
+8*(n^2+5*n-19)*a(n-3) -16*(n-3)*(3*n-10)*a(n-4) +32*(n-4)*(2*n-9)*a(n-5)=0.

Formalization: The entry gives the g.f. (1/2)*((1-4*x)^(-1/2) + (1-4*x^2)^(-1/2)) (Mark van Hoeij, Oct 30 2011), and this
closed form is used as the definition here. T and W are the formal power series over ℚ with
T^2 = 1-4*x, W^2 = 1-4*x^2 and constant terms 1 (the constant terms select the branches of the square
roots); and G is determined by 2*T*W*G = W + T, the closed form multiplied by 2*T*W (its constant
term 1 is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (20)*(126) + (-88)*(38) + (-4)*(10) + (248)*(4) + (-160)*(1) + (32)*(1) = 0.
-/

namespace OMA.S_oeis_a032123

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A032123, for n ≥ 5. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 W = 1 →
    2 * T * W * G = W + T →
    coeff 0 G = 1 →
    ∀ n : ℕ, 5 ≤ n →
      (-(n : ℚ) + (n : ℚ) ^ 2) * coeff n G + (-8 + 14 * (n : ℚ) - 6 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (76 - 56 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-152 + 40 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-480 + 304 * (n : ℚ) - 48 * (n : ℚ) ^ 2) * coeff (n - 4) G + (1152 - 544 * (n : ℚ) + 64 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a032123
