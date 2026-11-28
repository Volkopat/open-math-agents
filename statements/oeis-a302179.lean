import Mathlib

/-!
# OEIS A302179: Mathar's recurrence

Source: https://oeis.org/A302179 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Apr 09 2018), offset 0: The number of 3D walks of length n in an octant returning to
axis of origin. Data: 1, 1, 4, 9, 40, 120, 570, 1995, 9898, 38178, 195216, 805266, ... The formula section
states: Conjecture D-finite with recurrence 114*(n+5)*(n+4)*(n+2)*a(n)
+(-1669*n^3-12592*n^2-26619*n-13644)*a(n-1) +6*(19*n^3+2125*n^2+4411*n-1131)*a(n-2)
+8*(7895*n^3-9549*n^2-22925*n+14082)*a(n-3) +48*(-3553*n^3+14958*n^2-6986*n-16383)*a(n-4)
-432*(n-4)*(223*n^2-1110*n+1898)*a(n-5) +864*(n-5)*(779*n-1962)*(n-4)*a(n-6)
-518400*(n-5)*(n-6)*(n-4)*a(n-7)=0. - R. J. Mathar, Oct 29 2025

Formalization notes:
* Dershowitz (Touchard's Drunkard, Journal of Integer Sequences 20 (2017), Article 17.1.5, the entry's
  reference, which adds: “The sequence is type aac in Table 3.”) assigns each dimension a type. Section 4:
  “(a) For each dimension with its two opposing directions (like N and S above) that must stay to one side of
  the origin and return to zero (the promenade in our example) at the end”; “(c) For each dimension that must
  stay on one side of the origin (but need not return to zero at the end)”. The walk of type a in Section 1 is
  one in which “at each point along the way the number of N-steps that have been taken is never less than the
  number of S-steps, and, furthermore, in the end they are equal”. Section 5: “Table 3 provides computed
  initial terms for all three-dimensional walks with steps in all six directions (N/S/E/W/U/D)”; its row aac
  reads: octant (space), axis (back), 1, 1, 4, 9, 40, 120, 570, 1995, 9898, 38178, 195216, 805266, 4209084.
* So `a n` counts the words w of n steps among the six unit steps of ℤ³ (`step`) for which the walk from the
  origin keeps x ≥ 0, y ≥ 0 and z ≥ 0 at every point (type a in x and in y and type c in z: one side of the
  origin in each, the octant) and ends with x = 0 and y = 0 (type a), on the z-axis; z need not return (type
  c). `pt w t` is the point after the first t steps, t = 0, ..., n. Which axes carry which letters does not
  change the count.
* The reading reproduces the entry's data a(0..27): by brute force over all 6^n words for n ≤ 7 and by a
  dynamic program over (x, y, z) for all 28 terms; a(0..3) = 1, 1, 4, 9 also follow from the definition by
  kernel evaluation.
* The recurrence is stated in the integers for every n ≥ 7, the first n for which a(n-7) is a term (offset 0).
-/

namespace OMA.S_oeis_a302179

/-- The six unit steps of the cubic lattice ℤ³ as (x, y, z) displacements: ±x, ±y, ±z (N/S, E/W, U/D in
Dershowitz's notation). -/
def step : Fin 6 → ℤ × ℤ × ℤ :=
  ![(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- The point reached from the origin after the first t steps of the walk w. -/
def pt {n : ℕ} (w : Fin n → Fin 6) (t : ℕ) : ℤ × ℤ × ℤ :=
  ∑ i : Fin n, if (i : ℕ) < t then step (w i) else 0

/-- A302179(n): the n-step walks of type aac, which never leave the octant x ≥ 0, y ≥ 0, z ≥ 0 (type a in x and
in y, type c in z) and end on the z-axis, with x = 0 and y = 0 (type a); z need not return (type c). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 6 =>
    (∀ t ≤ n, 0 ≤ (pt w t).1 ∧ 0 ≤ (pt w t).2.1 ∧ 0 ≤ (pt w t).2.2) ∧ (pt w n).1 = 0 ∧ (pt w n).2.1 = 0)).card

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 7 ≤ n →
    114 * ((n : ℤ) + 5) * ((n : ℤ) + 4) * ((n : ℤ) + 2) * (a n : ℤ) +
      (-1669 * (n : ℤ) ^ 3 - 12592 * (n : ℤ) ^ 2 - 26619 * (n : ℤ) - 13644) * (a (n - 1) : ℤ) +
      6 * (19 * (n : ℤ) ^ 3 + 2125 * (n : ℤ) ^ 2 + 4411 * (n : ℤ) - 1131) * (a (n - 2) : ℤ) +
      8 * (7895 * (n : ℤ) ^ 3 - 9549 * (n : ℤ) ^ 2 - 22925 * (n : ℤ) + 14082) * (a (n - 3) : ℤ) +
      48 * (-3553 * (n : ℤ) ^ 3 + 14958 * (n : ℤ) ^ 2 - 6986 * (n : ℤ) - 16383) * (a (n - 4) : ℤ) -
      432 * ((n : ℤ) - 4) * (223 * (n : ℤ) ^ 2 - 1110 * (n : ℤ) + 1898) * (a (n - 5) : ℤ) +
      864 * ((n : ℤ) - 5) * (779 * (n : ℤ) - 1962) * ((n : ℤ) - 4) * (a (n - 6) : ℤ) -
      518400 * ((n : ℤ) - 5) * ((n : ℤ) - 6) * ((n : ℤ) - 4) * (a (n - 7) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a302179
