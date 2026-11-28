import Mathlib

/-!
# OEIS A302178: Mathar's recurrence

Source: https://oeis.org/A302178 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Apr 09 2018), offset 0: The number of 3D walks of semilength n in a quadrant returning
to the origin. Its link to Dershowitz (2017) adds: The sequence is type aab in Table 3. Data: 1, 4, 40, 570,
9898, 195216, 4209084, 96941130, 2349133930, 59272544760, ... The formula section states: Conjecture D-finite
with recurrence (n+1)*(n+2)^2*a(n) +2*(-29*n^3-39*n^2+8*n+6)*a(n-1) +36*(4*n-1)*(2*n-3)*(3*n-2)*a(n-2)
-648*(2*n-5)*(n-2)*(2*n-3)*a(n-3)=0. - R. J. Mathar, Oct 29 2025

Formalization notes:
* Dershowitz (Touchard's Drunkard, Journal of Integer Sequences 20 (2017), Article 17.1.5) assigns each
  dimension a type. Section 4: “(a) For each dimension with its two opposing directions (like N and S above)
  that must stay to one side of the origin and return to zero (the promenade in our example) at the end”; “(b)
  For each dimension that must return to zero at the end (but need not stay on one side of the origin)”;
  “Whenever there are only dimensions of types a and b, the number of walks is 0 for an odd number n of
  steps”. The walk of type a in Section 1 is one in which “at each point along the way the number of N-steps
  that have been taken is never less than the number of S-steps, and, furthermore, in the end they are equal”.
  Section 5: “Table 3 provides computed initial terms for all three-dimensional walks with steps in all six
  directions (N/S/E/W/U/D)”; its row aab reads: quad. (space), origin (back), 1, 0, 4, 0, 40, 0, 570, 0, 9898,
  0, 195216, 0, 4209084, 0, 96941130.
* So `a n` counts the words w of 2n steps (semilength n, as the name says; the table lists every length) among
  the six unit steps of ℤ³ (`step`) for which the walk from the origin keeps x ≥ 0 and y ≥ 0 at every point
  (type a twice: the quadrant) and returns to the origin (type a in x and y, type b in z). `pt w t` is the
  point after the first t steps, t = 0, ..., 2n. Which axes carry which letters does not change the count.
* The reading reproduces the entry's data a(0..18): by brute force over all 6^(2n) words for n ≤ 4 and by a
  dynamic program over (x, y, z) for all 19 terms (which also gives 0 at every odd length); a(0..2) = 1, 4, 40
  also follow from the definition by kernel evaluation.
* The recurrence is stated in the integers for every n ≥ 3, the first n for which a(n-3) is a term (offset 0).
-/

namespace OMA.S_oeis_a302178

/-- The six unit steps of the cubic lattice ℤ³ as (x, y, z) displacements: ±x, ±y, ±z (N/S, E/W, U/D in
Dershowitz's notation). -/
def step : Fin 6 → ℤ × ℤ × ℤ :=
  ![(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- The point reached from the origin after the first t steps of the walk w. -/
def pt {n : ℕ} (w : Fin n → Fin 6) (t : ℕ) : ℤ × ℤ × ℤ :=
  ∑ i : Fin n, if (i : ℕ) < t then step (w i) else 0

/-- A302178(n): the walks of semilength n (2n steps) of type aab, which never leave the quadrant x ≥ 0, y ≥ 0
(type a in x and in y) and return to the origin (type a in x and y, type b in z). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin (2 * n) → Fin 6 =>
    (∀ t ≤ 2 * n, 0 ≤ (pt w t).1 ∧ 0 ≤ (pt w t).2.1) ∧ pt w (2 * n) = 0)).card

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 1) * ((n : ℤ) + 2) ^ 2 * (a n : ℤ) +
      2 * (-29 * (n : ℤ) ^ 3 - 39 * (n : ℤ) ^ 2 + 8 * (n : ℤ) + 6) * (a (n - 1) : ℤ) +
      36 * (4 * (n : ℤ) - 1) * (2 * (n : ℤ) - 3) * (3 * (n : ℤ) - 2) * (a (n - 2) : ℤ) -
      648 * (2 * (n : ℤ) - 5) * ((n : ℤ) - 2) * (2 * (n : ℤ) - 3) * (a (n - 3) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a302178
