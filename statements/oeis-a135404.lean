import Mathlib

/-!
# OEIS A135404: the Gessel sequence

Source: https://oeis.org/A135404
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(m)` is the number of paths of length `2m` in the plane, starting and ending at `(0, 1)`, with
unit steps north, east, south, west, staying in the region `y > 0`, `x > -y`. Gessel's conjecture
(2001; now the Kauers–Koutschan–Zeilberger theorem):
`a(m) = 16^m (5/6)_m (1/2)_m / ((2)_m (5/3)_m)`, `(c)_m = c (c+1) ⋯ (c+m-1)`.

Conventions:
* A path is a list of `2m` steps (`Fin 4`: N, E, S, W); every point visited, including the start,
  must satisfy `y > 0` and `x > -y`. Rising factorials are `ascPochhammer` evaluated in `ℚ`.
-/

namespace OMA.S_oeis_a135404

/-- Displacement of a step. -/
def step (s : Fin 4) : ℤ × ℤ :=
  if s = 0 then (0, 1) else if s = 1 then (1, 0) else if s = 2 then (0, -1) else (-1, 0)

/-- Position after the first `j` steps of `w`, starting at `(0, 1)`. -/
def pos {L : ℕ} (w : Fin L → Fin 4) (j : ℕ) : ℤ × ℤ :=
  (0, 1) + ∑ i : Fin L, if (i : ℕ) < j then step (w i) else 0

/-- Number of admissible closed paths of length `2m`. -/
def a (m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * m) → Fin 4)).filter fun w =>
    pos w (2 * m) = (0, 1) ∧ ∀ j ≤ 2 * m, 0 < (pos w j).2 ∧ -(pos w j).2 < (pos w j).1).card

/-- Rising factorial `(c)_m`. -/
noncomputable def rf (c : ℚ) (m : ℕ) : ℚ := (ascPochhammer ℚ m).eval c

/-- Gessel's formula. -/
theorem main : ∀ m : ℕ,
    (a m : ℚ) = 16 ^ m * rf (5 / 6) m * rf (1 / 2) m / (rf 2 m * rf (5 / 3) m) := by
  sorry

end OMA.S_oeis_a135404
