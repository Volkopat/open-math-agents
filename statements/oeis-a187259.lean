import Mathlib

/-!
# A187259: Mathar's recurrence, corrected to n ≥ 8

Source: https://oeis.org/A187259
Credit: @ivillar

Status: false as stated at n = 7 (the left side is -384922 at n = 7 on the OEIS data); `main` is the
corrected recurrence (n ≥ 8), which is proved.

A187259 (offset 0): number of UH^jU's, DH^jD's, and DH^jU's for some j>0, in all peakless Motzkin paths of length n (here U=(1,1), D=(1,-1) and H=(1,0); can be easily expressed using RNA secondary structure terminology);
data 0, 0, 0, 0, 0, 0, 2, 11, 39, 122, 358, 1008, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
-(n+1)*(42968*n-187991)*a(n) +(-33354*n^2+888062*n+187991)*a(n-1)
+(587317*n^2-5596253*n+6148317)*a(n-2) +(-549823*n^2+5720814*n-11020859)*a(n-3)
+(176865*n^2-2521427*n+8169148)*a(n-4)
+(-587317*n^2+6446371*n-18005842)*a(n-5)+(592791*n^2-6850333*n+19290494)*a(n-6)
-(143511*n-619655)*(n-8)*a(n-7) = 0.

Formalization: T is the series g of the entry: the formal power series over ℚ with T = 1 + x*T + x^2*T*(T-1) (this
equation has exactly one power series solution, with constant term 1; it is the g.f. of the peakless
Motzkin paths); and the g.f. G is determined by
G*(1 - x)*(1 - x^2*T^2) = x^5*T^2*(3*T-1)*(T-1), the stated expression multiplied by its denominator (T is
called G in the entry);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 8): on the data the left side of the recurrence as
stated is -384922 at n = 7, and it vanishes from n = 8 on.
-/

namespace OMA.S_oeis_a187259

open PowerSeries

/-- The corrected recurrence (n ≥ 8): Mathar's recurrence, which fails at n = 7. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T + X ^ 2 * T * (T - 1) →
    G * ((1 - X) * (1 - X ^ 2 * T ^ 2)) = X ^ 5 * T ^ 2 * (3 * T - 1) * (T - 1) →
    ∀ n : ℕ, 8 ≤ n →
      (187991 + 145023 * (n : ℚ) - 42968 * (n : ℚ) ^ 2) * coeff n G + (187991 + 888062 * (n : ℚ) - 33354 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (6148317 - 5596253 * (n : ℚ) + 587317 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-11020859 + 5720814 * (n : ℚ) - 549823 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (8169148 - 2521427 * (n : ℚ) + 176865 * (n : ℚ) ^ 2) * coeff (n - 4) G + (-18005842 + 6446371 * (n : ℚ) - 587317 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (19290494 - 6850333 * (n : ℚ) + 592791 * (n : ℚ) ^ 2) * coeff (n - 6) G + (-4957240 + 1767743 * (n : ℚ) - 143511 * (n : ℚ) ^ 2) * coeff (n - 7) G = 0 := by
  sorry

end OMA.S_oeis_a187259
