import Mathlib

/-!
# A036837: Schoenheim bound L_1(n,n-5,n-6).

Source: https://oeis.org/A036837
Credit: @agchua

Conjecture in the formula section of A036837:
  Conjecture: G.f.: x^7*(4-x^9+5*x^8-10*x^7+10*x^6-5*x^5+2*x^4-5*x^3+10*x^2-9*x) /
  ((x^4+x^3+x^2+x+1)*(x-1)^6). - Maksym Voznyy (voznyy(AT)mail.ru), Jul 28 2009
Definition: the Schoenheim bound L(v,k,t) = ceiling(v/k * ceiling((v-1)/(k-1) * ... *
ceiling((v-t+1)/(k-t+1)) ... )), computed as L(v,k,0) = 1 and
L(v,k,t+1) = ceiling(v/k * L(v-1,k-1,t)), the quotients taken in ℚ; then a(n) = L(n, n-5, n-6)
for n ≥ 7 (offset 7; the listed terms 4, 11, 25, 50, 92, ... are recomputed by this rule).
The g.f. is stated as an identity of formal power series over ℚ for Sum_{n ≥ 7} a(n) x^n
(the coefficients below x^7 are 0, as the factor x^7 of the conjectured g.f. says).
-/

namespace OMA.S_oeis_a036837

/-- The Schoenheim bound: L v k 0 = 1 and L v k (t+1) = ceiling(v/k * L (v-1) (k-1) t). -/
noncomputable def L : ℕ → ℕ → ℕ → ℤ
  | _, _, 0 => 1
  | v, k, t + 1 => ⌈(v : ℚ) / (k : ℚ) * (L (v - 1) (k - 1) t : ℚ)⌉

/-- A036837: a(n) = L(n, n-5, n-6). -/
noncomputable def a (n : ℕ) : ℤ := L n (n - 5) (n - 6)

/-- The conjecture of Maksym Voznyy: Sum_{n ≥ 7} a(n) x^n is
x^7*(4-x^9+5*x^8-10*x^7+10*x^6-5*x^5+2*x^4-5*x^3+10*x^2-9*x)/((x^4+x^3+x^2+x+1)*(x-1)^6). -/
theorem main : PowerSeries.mk (fun n => if 7 ≤ n then (a n : ℚ) else 0) *
    ((PowerSeries.X ^ 4 + PowerSeries.X ^ 3 + PowerSeries.X ^ 2 + PowerSeries.X + 1) *
      (PowerSeries.X - 1) ^ 6) =
    PowerSeries.X ^ 7 * (4 - PowerSeries.X ^ 9 + 5 * PowerSeries.X ^ 8 - 10 * PowerSeries.X ^ 7 +
      10 * PowerSeries.X ^ 6 - 5 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 4 -
      5 * PowerSeries.X ^ 3 + 10 * PowerSeries.X ^ 2 - 9 * PowerSeries.X) := by
  sorry

end OMA.S_oeis_a036837
