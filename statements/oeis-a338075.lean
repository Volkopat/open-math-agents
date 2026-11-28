import Mathlib

/-!
# A338075: a conjectured generating function and recurrence

Source: https://oeis.org/A338075
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both
statements follow from the formula a(n) = A006480(n-1) + A006480(n) recorded in the entry, which is
used as the definition here.

A338075 (offset 0): diagonal terms in the expansion of (1+x*y*z)/(1-x-y-z);
data 1, 7, 96, 1770, 36330, 791406, 17909892, 416226096, 9864584730, 237338943270, ...

Conjectures from Robert Israel, Oct 25 2020:
(1) G.f.: (x + 1)*LegendreP(-1/3, 1 - 54*x).
(2) (-27*n^2 - 27*n - 6)*a(n + 1) + (-53*n^2 - 214*n - 173)*a(n + 2) + (-25*n^2 - 179*n - 319)*a(n + 3)
    + (n^2 + 8*n + 16)*a(n + 4) = 0.

Formalization: A006480(n) = (3n)!/(n!)^3 is the diagonal of 1/(1-x-y-z), and the entry records
a(n) = A006480(n-1) + A006480(n) for n > 0 (Seiichi Manyama, Oct 31 2020); with a(0) = 1 = A006480(0)
this is the definition of a(n) used here, with values in ℚ and t(n) = (3n)!/(n!)^3. The Legendre
function of degree -1/3 is LegendreP(-1/3, 1 - 2z) = 2F1(1/3, 2/3; 1; z), and
2F1(1/3, 2/3; 1; 27x) = Sum_n (3n)!/(n!)^3 x^n, so (1) is stated as the identity
Sum_n a(n) x^n = (1 + x) * Sum_n t(n) x^n of formal power series over ℚ. The recurrence (2) is stated
for all n ≥ 0. `main` is the conjunction of (1) and (2).
-/

namespace OMA.S_oeis_a338075

open PowerSeries

/-- t(n) = (3n)!/(n!)^3 (A006480). -/
def t (n : ℕ) : ℚ := ((3 * n).factorial : ℚ) / (n.factorial : ℚ) ^ 3

/-- a(0) = t(0) and a(n) = t(n-1) + t(n) for n > 0, the formula recorded in the entry. -/
def a (n : ℕ) : ℚ := if n = 0 then t 0 else t (n - 1) + t n

/-- The conjectured generating function and recurrence of A338075. -/
theorem main :
    (PowerSeries.mk a = (1 + X) * PowerSeries.mk t) ∧
    (∀ n : ℕ, (-27 * (n : ℚ) ^ 2 - 27 * (n : ℚ) - 6) * a (n + 1) +
      (-53 * (n : ℚ) ^ 2 - 214 * (n : ℚ) - 173) * a (n + 2) +
      (-25 * (n : ℚ) ^ 2 - 179 * (n : ℚ) - 319) * a (n + 3) +
      ((n : ℚ) ^ 2 + 8 * (n : ℚ) + 16) * a (n + 4) = 0) := by
  sorry

end OMA.S_oeis_a338075
