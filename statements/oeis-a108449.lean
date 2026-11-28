import Mathlib

/-!
# A108449: Mathar's recurrence

Source: https://oeis.org/A108449
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A108449 (offset 0): number of paths from (0,0) to (3n,0) that stay in the first quadrant (but may touch the horizontal axis), consisting of steps u=(2,1),U=(1,2), or d=(1,-1) and having no pyramids (a pyramid is a sequence u^pd^p or U^pd^(2p) for some positive integer p, starting at the x-axis);
data 1, 0, 4, 32, 252, 2112, 18484, 166976, 1545548, 14583808, 139774180, 1356966240, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
+n*(2*n+1)*(431*n-2895)*a(n) +2*(-9395*n^3+68622*n^2-64084*n+26109)*a(n-1)
+2*(59288*n^3-508196*n^2+1044822*n-574587)*a(n-2)
+2*(-94965*n^3+1070605*n^2-3607435*n+3485484)*a(n-3)
+4*(29036*n^3-351474*n^2+1402336*n-1970505)*a(n-4) +6*(-6703*n^3+63052*n^2-99178*n-237177)*a(n-5)
+6*(1012*n^3-14914*n^2+74580*n-127341)*a(n-6) +6*(1127*n^3-21429*n^2+135199*n-282762)*a(n-7)
+9*(29*n-165)*(2*n-15)*(n-8)*a(n-8) = 0.

Formalization: T is the series A of the entry (the g.f. of A027307): the formal power series over ℚ with
T = 1 + x*T^2 + x*T^3 (this equation has exactly one power series solution, with constant term 1); and
the g.f. G is determined by G*(1 + x - x*(1-x)*T*(1+T)) = 1 - x, the stated expression
(1-z)/[1+z-z(1-z)A(1+A)] multiplied by its denominator;
a(n) = [x^n] G. The recurrence involves a(n-8), so it is stated for n ≥ 8; it is checked by the data, for
example at n = 8: (75208)*(1545548) + (-1809990)*(166976) + (11229802)*(18484) + (-10954712)*(2112) + (6481116)*(252) + (-2563254)*(32) + (197682)*(4) + (26388)*(0) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a108449

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A108449, for n ≥ 8. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T ^ 2 + X * T ^ 3 →
    G * (1 + X - X * (1 - X) * T * (1 + T)) = 1 - X →
    ∀ n : ℕ, 8 ≤ n →
      (-2895 * (n : ℚ) - 5359 * (n : ℚ) ^ 2 + 862 * (n : ℚ) ^ 3) * coeff n G + (52218 - 128168 * (n : ℚ) + 137244 * (n : ℚ) ^ 2 - 18790 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-1149174 + 2089644 * (n : ℚ) - 1016392 * (n : ℚ) ^ 2 + 118576 * (n : ℚ) ^ 3) * coeff (n - 2) G + (6970968 - 7214870 * (n : ℚ) + 2141210 * (n : ℚ) ^ 2 - 189930 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-7882020 + 5609344 * (n : ℚ) - 1405896 * (n : ℚ) ^ 2 + 116144 * (n : ℚ) ^ 3) * coeff (n - 4) G + (-1423062 - 595068 * (n : ℚ) + 378312 * (n : ℚ) ^ 2 - 40218 * (n : ℚ) ^ 3) * coeff (n - 5) G +
        (-764046 + 447480 * (n : ℚ) - 89484 * (n : ℚ) ^ 2 + 6072 * (n : ℚ) ^ 3) * coeff (n - 6) G + (-1696572 + 811194 * (n : ℚ) - 128574 * (n : ℚ) ^ 2 + 6762 * (n : ℚ) ^ 3) * coeff (n - 7) G +
        (-178200 + 77355 * (n : ℚ) - 11061 * (n : ℚ) ^ 2 + 522 * (n : ℚ) ^ 3) * coeff (n - 8) G = 0 := by
  sorry

end OMA.S_oeis_a108449
