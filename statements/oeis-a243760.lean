import Mathlib

/-!
# A243760: Mathar's recurrence

Source: https://oeis.org/A243760
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A243760 (offset 0): expansion of (sqrt(8*x+4*sqrt(1-4*x)-3)-1)/(2*sqrt(1-4*x)-2);
data 0, 1, 1, 4, 11, 40, 138, 512, 1903, 7256, 27910, 108704, ...

Conjecture (R. J. Mathar, Jun 07 2016): D-finite with recurrence
245*n*(n-1)*(n+1)*a(n) -140*n*(n-1)*(28*n-53)*a(n-1) +4*(n-1)*(5812*n^2-29864*n+36585)*a(n-2)
+16*(-3368*n^3+35040*n^2-111784*n+110667)*a(n-3) +128*(-152*n^3-1224*n^2+14756*n-29655)*a(n-4)
+2048*(2*n-9)*(74*n^2-567*n+988)*a(n-5) -98304*(n-6)*(2*n-9)*(2*n-11)*a(n-6) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-4*x and constant term 1; W is the formal power
series with W^2 = 8*x + 4*T - 3 and constant term 1, that is W = sqrt(8x + 4*sqrt(1-4x) - 3) (the
constant terms select the branches of the square roots); and G is determined by G*(2*T - 2) = W - 1
(its constant term 0 follows from the other conditions and is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (51450)*(138) + (-483000)*(40) + (1332660)*(11) + (-417360)*(4) + (-2305920)*(1) + (1536000)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a243760

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A243760, for n ≥ 6. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 8 * X + 4 * T - 3 →
    coeff 0 W = 1 →
    G * (2 * T - 2) = W - 1 →
    coeff 0 G = 0 →
    ∀ n : ℕ, 6 ≤ n →
      (-245 * (n : ℚ) + 245 * (n : ℚ) ^ 3) * coeff n G + (-7420 * (n : ℚ) + 11340 * (n : ℚ) ^ 2 - 3920 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-146340 + 265796 * (n : ℚ) - 142704 * (n : ℚ) ^ 2 + 23248 * (n : ℚ) ^ 3) * coeff (n - 2) G + (1770672 - 1788544 * (n : ℚ) + 560640 * (n : ℚ) ^ 2 - 53888 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-3795840 + 1888768 * (n : ℚ) - 156672 * (n : ℚ) ^ 2 - 19456 * (n : ℚ) ^ 3) * coeff (n - 4) G + (-18210816 + 14497792 * (n : ℚ) - 3686400 * (n : ℚ) ^ 2 + 303104 * (n : ℚ) ^ 3) * coeff (n - 5) G +
        (58392576 - 33325056 * (n : ℚ) + 6291456 * (n : ℚ) ^ 2 - 393216 * (n : ℚ) ^ 3) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a243760
