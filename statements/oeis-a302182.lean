import Mathlib

/-!
# OEIS A302182: Mathar's recurrence

Source: https://oeis.org/A302182 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Apr 09 2018), offset 0: Number of 3D walks of type abc. See Dershowitz (2017) for
precise definition. Data: 1, 1, 5, 12, 62, 200, 1065, 3990, 21714, 89082, 492366, 2147376, ... The formula
section states: Conjecture D-finite with recurrence (n+2)*(n+3)^2*a(n) +4*(2*n^3+7*n^2+7*n+4)*a(n-1)
+4*(-25*n^3-28*n^2+54*n+35)*a(n-2) +32*(-10*n^3+26*n^2-23*n+40)*a(n-3) +48*(n-3)*(53*n^2-161*n+77)*a(n-4)
+576*(2*n+3)*(n-3)*(n-4)*a(n-5) -8640*(n-5)*(n-3)*(n-4)*a(n-6)=0. - R. J. Mathar, Oct 29 2025

Formalization notes:
* Dershowitz (Touchard's Drunkard, Journal of Integer Sequences 20 (2017), Article 17.1.5, the entry's
  reference) assigns each dimension a type. Section 4: “(a) For each dimension with its two opposing
  directions (like N and S above) that must stay to one side of the origin and return to zero (the promenade
  in our example) at the end”; “(b) For each dimension that must return to zero at the end (but need not stay
  on one side of the origin)”; “(c) For each dimension that must stay on one side of the origin (but need not
  return to zero at the end)”. The walk of type a in Section 1 is one in which “at each point along the way
  the number of N-steps that have been taken is never less than the number of S-steps, and, furthermore, in
  the end they are equal”. Section 5: “Table 3 provides computed initial terms for all three-dimensional walks
  with steps in all six directions (N/S/E/W/U/D)”; its row abc reads: quad. (space), axis (back), 1, 1, 5, 12,
  62, 200, 1065, 3990, 21714, 89082, 492366, 2147376, 12004740.
* So `a n` counts the words w of n steps among the six unit steps of ℤ³ (`step`) for which the walk from the
  origin keeps x ≥ 0 and z ≥ 0 at every point (type a in x and type c in z: one side of the origin in each,
  the quadrant) and ends with x = 0 (type a) and y = 0 (type b), on the z-axis; z need not return (type c).
  `pt w t` is the point after the first t steps, t = 0, ..., n. Which axes carry which letters does not change
  the count.
* The reading reproduces the entry's data a(0..25): by brute force over all 6^n words for n ≤ 7 and by a
  dynamic program over (x, y, z) for all 26 terms; a(0..3) = 1, 1, 5, 12 also follow from the definition by
  kernel evaluation.
* The recurrence is stated in the integers for every n ≥ 6, the first n for which a(n-6) is a term (offset 0).
-/

namespace OMA.S_oeis_a302182

/-- The six unit steps of the cubic lattice ℤ³ as (x, y, z) displacements: ±x, ±y, ±z (N/S, E/W, U/D in
Dershowitz's notation). -/
def step : Fin 6 → ℤ × ℤ × ℤ :=
  ![(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- The point reached from the origin after the first t steps of the walk w. -/
def pt {n : ℕ} (w : Fin n → Fin 6) (t : ℕ) : ℤ × ℤ × ℤ :=
  ∑ i : Fin n, if (i : ℕ) < t then step (w i) else 0

/-- A302182(n): the n-step walks of type abc, which never leave the quadrant x ≥ 0, z ≥ 0 (type a in x, type c
in z) and end on the z-axis, with x = 0 (type a) and y = 0 (type b); z need not return (type c). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 6 =>
    (∀ t ≤ n, 0 ≤ (pt w t).1 ∧ 0 ≤ (pt w t).2.2) ∧ (pt w n).1 = 0 ∧ (pt w n).2.1 = 0)).card

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) + 2) * ((n : ℤ) + 3) ^ 2 * (a n : ℤ) +
      4 * (2 * (n : ℤ) ^ 3 + 7 * (n : ℤ) ^ 2 + 7 * (n : ℤ) + 4) * (a (n - 1) : ℤ) +
      4 * (-25 * (n : ℤ) ^ 3 - 28 * (n : ℤ) ^ 2 + 54 * (n : ℤ) + 35) * (a (n - 2) : ℤ) +
      32 * (-10 * (n : ℤ) ^ 3 + 26 * (n : ℤ) ^ 2 - 23 * (n : ℤ) + 40) * (a (n - 3) : ℤ) +
      48 * ((n : ℤ) - 3) * (53 * (n : ℤ) ^ 2 - 161 * (n : ℤ) + 77) * (a (n - 4) : ℤ) +
      576 * (2 * (n : ℤ) + 3) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 5) : ℤ) -
      8640 * ((n : ℤ) - 5) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 6) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a302182
