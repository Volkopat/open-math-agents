import Mathlib

/-!
# OEIS A302187: Mathar's recurrence

Source: https://oeis.org/A302187 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Apr 09 2018), offset 0: Number of 3D walks of type bcc. See Dershowitz (2017) for
precise definition. Data: 1, 2, 8, 30, 138, 620, 3060, 14910, 76650, 390852, 2063376, 10832052, ... The
formula section states: Conjecture D-finite with recurrence (n+1)*(n+2)^2*a(n) +2*(7*n^3-17*n-6)*a(n-1)
-4*(4*n-1)*(4*n^2+9*n-12)*a(n-2) +8*(-70*n^3+330*n^2-461*n+225)*a(n-3) +48*(n-3)*(23*n^2-66*n+64)*a(n-4)
+288*(7*n-17)*(n-3)*(n-4)*a(n-5) -3456*(n-5)*(n-3)*(n-4)*a(n-6)=0. - R. J. Mathar, Oct 29 2025

Formalization notes:
* Dershowitz (Touchard's Drunkard, Journal of Integer Sequences 20 (2017), Article 17.1.5, the entry's
  reference) assigns each dimension a type. Section 4: “(b) For each dimension that must return to zero at the
  end (but need not stay on one side of the origin)”; “(c) For each dimension that must stay on one side of
  the origin (but need not return to zero at the end)”. Section 5: “Table 3 provides computed initial terms
  for all three-dimensional walks with steps in all six directions (N/S/E/W/U/D)”; its row bcc reads: quad.
  (space), plane (back), 1, 2, 8, 30, 138, 620, 3060, 14910, 76650, 390852, 2063376, 10832052.
* So `a n` counts the words w of n steps among the six unit steps of ℤ³ (`step`) for which the walk from the
  origin keeps y ≥ 0 and z ≥ 0 at every point (type c in y and in z: one side of the origin in each, the
  quadrant) and ends with x = 0 (type b in x: back to the plane x = 0); y and z need not return. `pt w t` is
  the point after the first t steps, t = 0, ..., n. Which axes carry which letters does not change the count.
* The reading reproduces the entry's data a(0..25): by brute force over all 6^n words for n ≤ 7 and by a
  dynamic program over (x, y, z) for all 26 terms; a(0..3) = 1, 2, 8, 30 also follow from the definition by
  kernel evaluation.
* The recurrence is stated in the integers for every n ≥ 6, the first n for which a(n-6) is a term (offset 0).
-/

namespace OMA.S_oeis_a302187

/-- The six unit steps of the cubic lattice ℤ³ as (x, y, z) displacements: ±x, ±y, ±z (N/S, E/W, U/D in
Dershowitz's notation). -/
def step : Fin 6 → ℤ × ℤ × ℤ :=
  ![(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- The point reached from the origin after the first t steps of the walk w. -/
def pt {n : ℕ} (w : Fin n → Fin 6) (t : ℕ) : ℤ × ℤ × ℤ :=
  ∑ i : Fin n, if (i : ℕ) < t then step (w i) else 0

/-- A302187(n): the n-step walks of type bcc, which never leave the quadrant y ≥ 0, z ≥ 0 (type c in y and in
z) and end in the plane x = 0 (type b in x); y and z need not return (type c). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 6 =>
    (∀ t ≤ n, 0 ≤ (pt w t).2.1 ∧ 0 ≤ (pt w t).2.2) ∧ (pt w n).1 = 0)).card

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) + 1) * ((n : ℤ) + 2) ^ 2 * (a n : ℤ) + 2 * (7 * (n : ℤ) ^ 3 - 17 * (n : ℤ) - 6) * (a (n - 1) : ℤ) -
      4 * (4 * (n : ℤ) - 1) * (4 * (n : ℤ) ^ 2 + 9 * (n : ℤ) - 12) * (a (n - 2) : ℤ) +
      8 * (-70 * (n : ℤ) ^ 3 + 330 * (n : ℤ) ^ 2 - 461 * (n : ℤ) + 225) * (a (n - 3) : ℤ) +
      48 * ((n : ℤ) - 3) * (23 * (n : ℤ) ^ 2 - 66 * (n : ℤ) + 64) * (a (n - 4) : ℤ) +
      288 * (7 * (n : ℤ) - 17) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 5) : ℤ) -
      3456 * ((n : ℤ) - 5) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 6) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a302187
