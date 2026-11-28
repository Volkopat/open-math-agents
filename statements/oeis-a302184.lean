import Mathlib

/-!
# OEIS A302184: Mathar's recurrence

Source: https://oeis.org/A302184 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Apr 09 2018), offset 0: Number of 3D walks of type abe. See Dershowitz (2017) for
precise definition. Data: 1, 2, 7, 26, 108, 472, 2159, 10194, 49396, 244328, 1229308, 6273896, ... The formula
section states: Conjecture D-finite with recurrence (n+2)^2*a(n) +2*(-3*n^2-5*n-1)*a(n-1)
-4*(n+3)*(n-1)*a(n-2) +24*(n-1)*(n-2)*a(n-3)=0. - R. J. Mathar, Oct 29 2025

Formalization notes:
* Dershowitz (Touchard's Drunkard, Journal of Integer Sequences 20 (2017), Article 17.1.5, the entry's
  reference) assigns each dimension a type. Section 4: “(a) For each dimension with its two opposing
  directions (like N and S above) that must stay to one side of the origin and return to zero (the promenade
  in our example) at the end”; “(b) For each dimension that must return to zero at the end (but need not stay
  on one side of the origin)”; “e is short for dd, meaning that there are no restrictions on steps in that
  dimension”. The walk of type a in Section 1 is one in which “at each point along the way the number of
  N-steps that have been taken is never less than the number of S-steps, and, furthermore, in the end they are
  equal”. Section 5: “Table 3 provides computed initial terms for all three-dimensional walks with steps in
  all six directions (N/S/E/W/U/D)”; its row abe reads: half (space), axis (back), 1, 2, 7, 26, 108, 472,
  2159, 10194, 49396, 244328, 1229308, 6273896.
* So `a n` counts the words w of n steps among the six unit steps of ℤ³ (`step`) for which the walk from the
  origin keeps x ≥ 0 at every point (type a: one side of the origin, the half-space) and ends with x = 0 (type
  a) and y = 0 (type b), on the z-axis; z is unrestricted (type e). `pt w t` is the point after the first t
  steps, t = 0, ..., n. Which axis carries which letter does not change the count.
* The reading reproduces the entry's data a(0..25): by brute force over all 6^n words for n ≤ 7 and by a
  dynamic program over (x, y) for all 26 terms; a(0..3) = 1, 2, 7, 26 also follow from the definition by
  kernel evaluation.
* The recurrence is stated in the integers for every n ≥ 3, the first n for which a(n-3) is a term (offset 0).
-/

namespace OMA.S_oeis_a302184

/-- The six unit steps of the cubic lattice ℤ³ as (x, y, z) displacements: ±x, ±y, ±z (N/S, E/W, U/D in
Dershowitz's notation). -/
def step : Fin 6 → ℤ × ℤ × ℤ :=
  ![(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- The point reached from the origin after the first t steps of the walk w. -/
def pt {n : ℕ} (w : Fin n → Fin 6) (t : ℕ) : ℤ × ℤ × ℤ :=
  ∑ i : Fin n, if (i : ℕ) < t then step (w i) else 0

/-- A302184(n): the n-step walks of type abe, which never leave the half-space x ≥ 0 (type a in x) and end on
the z-axis, with x = 0 (type a) and y = 0 (type b); z is unrestricted (type e). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 6 =>
    (∀ t ≤ n, 0 ≤ (pt w t).1) ∧ (pt w n).1 = 0 ∧ (pt w n).2.1 = 0)).card

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 2) ^ 2 * (a n : ℤ) + 2 * (-3 * (n : ℤ) ^ 2 - 5 * (n : ℤ) - 1) * (a (n - 1) : ℤ) -
      4 * ((n : ℤ) + 3) * ((n : ℤ) - 1) * (a (n - 2) : ℤ) +
      24 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (a (n - 3) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a302184
