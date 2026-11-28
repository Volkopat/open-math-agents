import Mathlib

/-!
# A161006: Convolution of A000108 (Catalan numbers) with A126120 (Catalan numbers interpolated with 0's).

Source: https://oeis.org/A161006 (conjecture by R. J. Mathar, Oct 04 2014)

`a(n)` (offset 0) is the `n`-th term of the convolution of the Catalan numbers A000108 with A126120
(the Catalan numbers interpolated with 0's: `C(k)` at index `2k`, `0` at odd indices). The g.f. of
A000108 is `c(x)` and the g.f. of A126120 is `c(x^2)`, so the convolution has g.f. `c(x) c(x^2)` (as in
the entry). Over `ℚ`, `c` is Mathlib's `catalanSeries` mapped to `ℚ` and `c(x^2)` is
`PowerSeries.subst`.

The conjecture, stated for `n >= 7` (where every index is defined):
Conjecture: -(47*n-42)*(n+3)*(n+2)*(n+1)*a(n) + 2*(n+2)*(n+1)*(270*n^2 - 523*n + 126)*a(n-1) - 8*(n+1)*(211*n^3 - 1022*n^2 + 946*n + 63)*a(n-2) + 8*(-212*n^4 - 326*n^3 + 2489*n^2 - 1636*n + 126)*a(n-3) + 16*(985*n^4 - 8154*n^3 + 23771*n^2 - 28164*n + 11151)*a(n-4) + 32*(-386*n^4 + 5771*n^3 - 29314*n^2 + 60721*n - 43533)*a(n-5) - 64*(n-4)*(2*n-9)*(258*n^2 - 1193*n + 1267)*a(n-6) + 128*(n-5)*(2*n-9)*(2*n-11)*(82*n-203)*a(n-7) = 0.
-/

namespace OMA.S_oeis_a161006

open PowerSeries

/-- The generating function `c(x)` of the Catalan numbers A000108 (over `ℚ`). -/
noncomputable def c : PowerSeries ℚ := PowerSeries.map (Nat.castRingHom ℚ) catalanSeries

/-- The generating function of the sequence, `c(x) c(x^2)`. -/
noncomputable def A : PowerSeries ℚ := c * c.subst (X ^ 2)

theorem main : ∀ n : ℕ, 7 ≤ n →
      (-(47*(n : ℚ)-42)*((n : ℚ)+3)*((n : ℚ)+2)*((n : ℚ)+1)) * coeff n A +
        (2*((n : ℚ)+2)*((n : ℚ)+1)*(270*(n : ℚ)^2 - 523*(n : ℚ) + 126)) * coeff (n - 1) A +
        (-8*((n : ℚ)+1)*(211*(n : ℚ)^3 - 1022*(n : ℚ)^2 + 946*(n : ℚ) + 63)) * coeff (n - 2) A +
        (8*(-212*(n : ℚ)^4 - 326*(n : ℚ)^3 + 2489*(n : ℚ)^2 - 1636*(n : ℚ) + 126)) * coeff (n - 3) A +
        (16*(985*(n : ℚ)^4 - 8154*(n : ℚ)^3 + 23771*(n : ℚ)^2 - 28164*(n : ℚ) + 11151)) * coeff (n - 4) A +
        (32*(-386*(n : ℚ)^4 + 5771*(n : ℚ)^3 - 29314*(n : ℚ)^2 + 60721*(n : ℚ) - 43533)) * coeff (n - 5) A +
        (-64*((n : ℚ)-4)*(2*(n : ℚ)-9)*(258*(n : ℚ)^2 - 1193*(n : ℚ) + 1267)) * coeff (n - 6) A +
        (128*((n : ℚ)-5)*(2*(n : ℚ)-9)*(2*(n : ℚ)-11)*(82*(n : ℚ)-203)) * coeff (n - 7) A = 0 := by
  sorry

end OMA.S_oeis_a161006
