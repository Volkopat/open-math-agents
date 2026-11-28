import Mathlib

/-!
# OEIS A159807: e.g.f. and recurrence for the numerators of Hermite(n, 3/22)

Source: https://oeis.org/A159807 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Nov 12 2009), offset 0: Numerator of Hermite(n, 3/22). Example:
numerators of 1, 3/11, -233/121, -2151/1331, 162705/14641, ... Formula: From Vincenzo Librandi,
Jan 20 2017: Conjecture: E.g.f.: exp(-x*(121*x-3)). D-finite with recurrence
a(n) = 3*a(n-1) - 242*(n-1)*a(n-2). [DLMF] Corrected Feb 06 2021.

Formalization notes:
* Hermite(n, x) is the physicists' Hermite polynomial (Mathematica HermiteH, PARI polhermite, as
  in the entry's programs), given by H_0 = 1, H_1 = 2x, H_(n+2) = 2x H_(n+1) - 2(n+1) H_n; the
  example values above are reproduced (H_2(3/22) = -233/121).
* The numerator is `Rat.num`, which carries the sign.
* `main` is the conjunction of both parts: the e.g.f. identity in Q[[x]], where exp(-x(121x - 3))
  is `PowerSeries.exp` with -x(121x - 3) substituted (`PowerSeries.subst`), and the recurrence for
  every n >= 2.
* Controls proved in the proof file: a(0..4) = 1, 3, -233, -2151, 162705.
-/

namespace OMA.S_oeis_a159807

/-- The physicists' Hermite polynomial H_n evaluated at x. -/
def H : ℕ → ℚ → ℚ
  | 0, _ => 1
  | 1, x => 2 * x
  | n + 2, x => 2 * x * H (n + 1) x - 2 * (n + 1) * H n x

/-- A159807(n): the numerator of Hermite(n, 3/22). -/
def a (n : ℕ) : ℤ := (H n (3 / 22)).num

open PowerSeries in
/-- Librandi's e.g.f. and the recurrence. -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
      (exp ℚ).subst (-(X * (121 * X - 3)) : PowerSeries ℚ) ∧
    ∀ n : ℕ, 2 ≤ n → a n = 3 * a (n - 1) - 242 * (n - 1 : ℕ) * a (n - 2) := by
  sorry

end OMA.S_oeis_a159807
