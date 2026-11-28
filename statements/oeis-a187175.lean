import Mathlib

/-!
# A187175: Number of 5-step left-handed knight's tours (moves only out two, left one) on an n X n board summed over all starting positions.

Source: https://oeis.org/A187175

Conjectures listed in the entry:
  Empirical: a(n) = 100*n^2 - 920*n + 1984 for n>7.
  G.f.: 4*x^5*(2 - x)*(2 + 12*x + 18*x^2 + 15*x^3 + 3*x^4) / (1 - x)^3 (conjectured). - Colin Barker, Apr 22 2018

Conventions:
* The board is `Fin n × Fin n`. A left-handed knight moves two squares in one of the four directions
  and then one square to the left of that direction, i.e. by one of the displacements
  (2, 1), (-1, 2), (-2, -1), (1, -2) (the mirror-image convention gives the same counts).
* As in the entry's example (the cells of a 5-step tour are numbered 1..5), a 5-step tour is a
  sequence of 5 distinct squares, each obtained from the previous one by a left-handed knight move.
  Every tour is counted once, so the count is summed over all starting positions.
* Offset 1 (the definition gives a(0) = 0). The g.f. is the ordinary generating function, stated
  as an identity of formal power series over ℚ with the denominator multiplied out.

Prior art: a written proof with a verification script for this conjecture (published 26 November
2026) is referenced in the withdrawn statement PR #16335; this formalization follows that result.
-/

namespace OMA.S_oeis_a187175

open PowerSeries

/-- A left-handed knight move. -/
def IsMove (d : ℤ × ℤ) : Prop := d = (2, 1) ∨ d = (-1, 2) ∨ d = (-2, -1) ∨ d = (1, -2)

/-- A 5-step tour: 5 distinct squares, consecutive ones a left-handed knight move apart. -/
def IsTour (n : ℕ) (f : Fin 5 → Fin n × Fin n) : Prop :=
  Function.Injective f ∧ ∀ i : Fin 4,
    IsMove (((f i.succ).1 : ℤ) - (f i.castSucc).1, ((f i.succ).2 : ℤ) - (f i.castSucc).2)

/-- A187175(n). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {f : Fin 5 → Fin n × Fin n // IsTour n f}

theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 100 * n ^ 2 - 920 * n + 1984) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 3 =
      4 * X ^ 5 * (2 - X) * (2 + 12 * X + 18 * X ^ 2 + 15 * X ^ 3 + 3 * X ^ 4) := by
  sorry

end OMA.S_oeis_a187175
