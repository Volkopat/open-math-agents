import Mathlib

/-!
# A187177: Number of 7-step left-handed knight's tours (moves only out two, left one) on an n X n board summed over all starting positions.

Source: https://oeis.org/A187177

Conjectures listed in the entry:
  Empirical: a(n) = 780*n^2 - 9880*n + 29384 for n>11.
  G.f.: 4*x^6*(4 + 80*x + 136*x^2 + 143*x^3 + 85*x^4 + 19*x^5 - 43*x^6 - 29*x^7 - 5*x^8) / (1 - x)^3 (conjectured). - Colin Barker, Apr 22 2018

Conventions:
* The board is `Fin n × Fin n`. A left-handed knight moves two squares in one of the four directions
  and then one square to the left of that direction, i.e. by one of the displacements
  (2, 1), (-1, 2), (-2, -1), (1, -2) (the mirror-image convention gives the same counts).
* As in the entry's example (the cells of a 5-step tour are numbered 1..5), a 7-step tour is a
  sequence of 7 distinct squares, each obtained from the previous one by a left-handed knight move.
  Every tour is counted once, so the count is summed over all starting positions.
* Offset 1 (the definition gives a(0) = 0). The g.f. is the ordinary generating function, stated
  as an identity of formal power series over ℚ with the denominator multiplied out.

Prior art: a written proof with a verification script for this conjecture (published 26 November
2026) is referenced in the withdrawn statement PR #16605; this formalization follows that result.
-/

namespace OMA.S_oeis_a187177

open PowerSeries

/-- A left-handed knight move. -/
def IsMove (d : ℤ × ℤ) : Prop := d = (2, 1) ∨ d = (-1, 2) ∨ d = (-2, -1) ∨ d = (1, -2)

/-- A 7-step tour: 7 distinct squares, consecutive ones a left-handed knight move apart. -/
def IsTour (n : ℕ) (f : Fin 7 → Fin n × Fin n) : Prop :=
  Function.Injective f ∧ ∀ i : Fin 6,
    IsMove (((f i.succ).1 : ℤ) - (f i.castSucc).1, ((f i.succ).2 : ℤ) - (f i.castSucc).2)

/-- A187177(n). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {f : Fin 7 → Fin n × Fin n // IsTour n f}

theorem main :
    (∀ n : ℕ, 11 < n → (a n : ℤ) = 780 * n ^ 2 - 9880 * n + 29384) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 3 =
      4 * X ^ 6 * (4 + 80 * X + 136 * X ^ 2 + 143 * X ^ 3 + 85 * X ^ 4 + 19 * X ^ 5 - 43 * X ^ 6 - 29 * X ^ 7 - 5 * X ^ 8) := by
  sorry

end OMA.S_oeis_a187177
