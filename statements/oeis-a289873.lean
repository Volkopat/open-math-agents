import Mathlib

/-!
# OEIS A289873: Barker's g.f. for (n^2 - (n mod 6 - 3)^2)/3

Source: https://oeis.org/A289873 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Hugo Pfoertner, Jul 14 2017), offset 2: Related to perfect Wichmann rulers: a(n) = ( n^2 - (mod(n,
6) - 3)^2 ) / 3. The formula section states: G.f.: x^2*(1 + x - x^2)*(1 + x^2 - x^3 + 2*x^4 + x^5)
/ ((1 - x)^3*(1 + x)*(1 - x + x^2)*(1 + x + x^2)) (conjectured). - Colin Barker, Jul 14 2017

Formalization notes:
* a(n) is computed in Q from the entry's name; mod(n, 6) is the remainder of n mod 6.
* With offset 2, the g.f. is the series Sum_{n >= 2} a(n) x^n; the identity A(x) = N(x)/D(x) is
  stated as A(x)*D(x) = N(x) in Q[[x]], which is equivalent because D has constant term 1.
* Controls: the definition gives a(2..8) = 1, 3, 5, 7, 9, 15, 21, as in the entry.
-/

namespace OMA.S_oeis_a289873

/-- A289873(n) = (n^2 - (n mod 6 - 3)^2)/3. -/
def a (n : ℕ) : ℚ := ((n : ℚ) ^ 2 - (((n % 6 : ℕ) : ℚ) - 3) ^ 2) / 3

open PowerSeries in
/-- Barker's conjecture: the g.f. of a(n), n >= 2. -/
theorem main :
    PowerSeries.mk (fun n => if n < 2 then (0 : ℚ) else a n) *
        ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2)) =
      X ^ 2 * (1 + X - X ^ 2) * (1 + X ^ 2 - X ^ 3 + 2 * X ^ 4 + X ^ 5) := by
  sorry

end OMA.S_oeis_a289873
