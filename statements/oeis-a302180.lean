import Mathlib

/-!
# OEIS A302180: Mathar's recurrence

Source: https://oeis.org/A302180 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Apr 09 2018), offset 0: Number of 3D walks of type aad. See Dershowitz (2017) for
precise definition. Data: 1, 1, 3, 7, 23, 71, 251, 883, 3305, 12505, 48895, 193755, ... The formula section
states: Conjecture D-finite with recurrence (n+4)*(n+2)*a(n) +3*(-n^2-3*n-1)*a(n-1) -13*(n-1)*(n+1)*a(n-2)
+15*(n-1)*(n-2)*a(n-3)=0. - R. J. Mathar, Oct 29 2025

Formalization notes:
* Dershowitz (Touchard's Drunkard, Journal of Integer Sequences 20 (2017), Article 17.1.5, the entry's
  reference) assigns each dimension a type. Section 4: “(a) For each dimension with its two opposing
  directions (like N and S above) that must stay to one side of the origin and return to zero (the promenade
  in our example) at the end”; “(b) For each dimension that must return to zero at the end (but need not stay
  on one side of the origin)”; “(d) For any remaining r unrestricted directions (like E and W above), there is
  an exponential factor r^{n-m}”; “e is short for dd, meaning that there are no restrictions on steps in that
  dimension, whereas d means that the dimension is one-way only”. The walk of type a in Section 1 is one in
  which “at each point along the way the number of N-steps that have been taken is never less than the number
  of S-steps, and, furthermore, in the end they are equal”. Table 3 lists the three-dimensional walks; its row
  aad reads: octant (space), axis (back), 1, 1, 3, 7, 23, 71, 251, 883, 3305, 12505, 48895, 193755, 783355,
  3205931.
* So `a n` counts the words w of n steps among the five steps ±x, ±y, +z (`step`) for which the walk from the
  origin keeps x ≥ 0 and y ≥ 0 at every point (type a twice: one side of the origin in x and in y) and ends
  with x = 0 and y = 0 (type a), on the z-axis; z moves one way only (type d). `pt w t` is the point after the
  first t steps, t = 0, ..., n. Which axis carries which letter does not change the count. F. Byramji's
  comment in the entry describes the same count with the z-steps as horizontal steps (1, 0, 0) and the other
  four as (1, ±1, 0), (1, 0, ±1).
* A one-way dimension has a single direction (r = 1 in the factor r^{n-m}), so these walks use five of the six
  directions, although Section 5 introduces Table 3 as walks with steps in all six directions: the table's
  terms (a(1) = 1) agree with five steps and not with six.
* The reading reproduces the entry's data a(0..27): by brute force over all 5^n words for n ≤ 8 and by a
  dynamic program over (x, y) for all 28 terms; a(0..3) = 1, 1, 3, 7 also follow from the definition by kernel
  evaluation.
* The recurrence is stated in the integers for every n ≥ 3, the first n for which a(n-3) is a term (offset 0).
-/

namespace OMA.S_oeis_a302180

/-- The five steps of the walk as (x, y, z) displacements: ±x, ±y and +z only (N/S, E/W and U in
Dershowitz's notation; the third dimension is one-way). -/
def step : Fin 5 → ℤ × ℤ × ℤ :=
  ![(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1)]

/-- The point reached from the origin after the first t steps of the walk w. -/
def pt {n : ℕ} (w : Fin n → Fin 5) (t : ℕ) : ℤ × ℤ × ℤ :=
  ∑ i : Fin n, if (i : ℕ) < t then step (w i) else 0

/-- A302180(n): the n-step walks of type aad, which never leave the quadrant x ≥ 0, y ≥ 0 (type a in x and in
y) and end on the z-axis, with x = 0 and y = 0 (type a); z only increases (type d). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 5 =>
    (∀ t ≤ n, 0 ≤ (pt w t).1 ∧ 0 ≤ (pt w t).2.1) ∧ (pt w n).1 = 0 ∧ (pt w n).2.1 = 0)).card

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 4) * ((n : ℤ) + 2) * (a n : ℤ) + 3 * (-(n : ℤ) ^ 2 - 3 * (n : ℤ) - 1) * (a (n - 1) : ℤ) -
      13 * ((n : ℤ) - 1) * ((n : ℤ) + 1) * (a (n - 2) : ℤ) +
      15 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (a (n - 3) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a302180
