import Mathlib

/-!
# A187176: Number of 6-step left-handed knight's tours (moves only out two, left one) on an n X n board summed over all starting positions.

Source: https://oeis.org/A187176

Conjectures listed in the entry:
  Empirical: a(n) = 284*n^2 - 3100*n + 7944 for n>9.
  G.f.: 8*x^6*(11 + 29*x + 27*x^2 + 18*x^3 - 3*x^4 - 9*x^5 - 2*x^6) / (1 - x)^3 (conjectured). - Colin Barker, Apr 22 2018

Conventions:
* The board is `Fin n × Fin n`. A left-handed knight moves two squares in one of the four directions
  and then one square to the left of that direction, i.e. by one of the displacements
  (2, 1), (-1, 2), (-2, -1), (1, -2) (the mirror-image convention gives the same counts).
* As in the entry's example (the cells of a 5-step tour are numbered 1..5), a 6-step tour is a
  sequence of 6 distinct squares, each obtained from the previous one by a left-handed knight move.
  Every tour is counted once, so the count is summed over all starting positions.
* Offset 1 (the definition gives a(0) = 0). The g.f. is the ordinary generating function, stated
  as an identity of formal power series over ℚ with the denominator multiplied out.

Prior art: a written proof with a verification script for this conjecture (published 26 November
2026) is referenced in the withdrawn statement PR #16360; this formalization follows that result.
-/

namespace OMA.S_oeis_a187176

open PowerSeries

/-- A left-handed knight move. -/
def IsMove (d : ℤ × ℤ) : Prop := d = (2, 1) ∨ d = (-1, 2) ∨ d = (-2, -1) ∨ d = (1, -2)

/-- A 6-step tour: 6 distinct squares, consecutive ones a left-handed knight move apart. -/
def IsTour (n : ℕ) (f : Fin 6 → Fin n × Fin n) : Prop :=
  Function.Injective f ∧ ∀ i : Fin 5,
    IsMove (((f i.succ).1 : ℤ) - (f i.castSucc).1, ((f i.succ).2 : ℤ) - (f i.castSucc).2)

/-- A187176(n). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {f : Fin 6 → Fin n × Fin n // IsTour n f}

theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 284 * n ^ 2 - 3100 * n + 7944) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 3 =
      8 * X ^ 6 * (11 + 29 * X + 27 * X ^ 2 + 18 * X ^ 3 - 3 * X ^ 4 - 9 * X ^ 5 - 2 * X ^ 6) := by
  sorry

end OMA.S_oeis_a187176
