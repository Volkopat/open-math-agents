import Mathlib

/-!
# OEIS A302181: Mathar's recurrence

Source: https://oeis.org/A302181 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Apr 09 2018), offset 0: Number of 3D walks of type abb. See Dershowitz (2017) for
precise definition. Data: 1, 5, 62, 1065, 21714, 492366, 12004740, 308559537, 8255788970, 227976044010, ...
The formula section states: Conjecture D-finite with recurrence (n+1)^3*a(n) -2*(2*n-1)*(10*n^2+10*n+3)*a(n-1)
+36*n*(2*n-1)*(2*n-3)*a(n-2)=0. - R. J. Mathar, Oct 29 2025

Formalization notes:
* Dershowitz (Touchard's Drunkard, Journal of Integer Sequences 20 (2017), Article 17.1.5, the entry's
  reference) assigns each dimension a type. Section 4: “(a) For each dimension with its two opposing
  directions (like N and S above) that must stay to one side of the origin and return to zero (the promenade
  in our example) at the end”; “(b) For each dimension that must return to zero at the end (but need not stay
  on one side of the origin)”; “Whenever there are only dimensions of types a and b, the number of walks is 0
  for an odd number n of steps”. The walk of type a in Section 1 is one in which “at each point along the way
  the number of N-steps that have been taken is never less than the number of S-steps, and, furthermore, in
  the end they are equal”. Section 5: “Table 3 provides computed initial terms for all three-dimensional walks
  with steps in all six directions (N/S/E/W/U/D)”; its row abb reads: half (space), origin (back), 1, 0, 5, 0,
  62, 0, 1065, 0, 21714, 0, 492366, 0, 12004740, 0, 308559537.
* So the terms of Table 3 are indexed by the length, and the entry lists those of even length: `a n` counts
  the words w of 2n steps among the six unit steps of ℤ³ (`step`) for which the walk from the origin keeps x ≥
  0 at every point (type a: one side of the origin, the half-space) and returns to the origin (type a in x,
  type b in y and in z). `pt w t` is the point after the first t steps, t = 0, ..., 2n. Which axis carries
  which letter does not change the count.
* The reading reproduces the entry's data a(0..18): by brute force over all 6^(2n) words for n ≤ 4 and by a
  dynamic program over (x, y, z) for all 19 terms (which also gives 0 at every odd length); a(0..2) = 1, 5, 62
  also follow from the definition by kernel evaluation.
* The recurrence is stated in the integers for every n ≥ 2, the first n for which a(n-2) is a term (offset 0).
-/

namespace OMA.S_oeis_a302181

/-- The six unit steps of the cubic lattice ℤ³ as (x, y, z) displacements: ±x, ±y, ±z (N/S, E/W, U/D in
Dershowitz's notation). -/
def step : Fin 6 → ℤ × ℤ × ℤ :=
  ![(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- The point reached from the origin after the first t steps of the walk w. -/
def pt {n : ℕ} (w : Fin n → Fin 6) (t : ℕ) : ℤ × ℤ × ℤ :=
  ∑ i : Fin n, if (i : ℕ) < t then step (w i) else 0

/-- A302181(n): the walks of type abb with 2n steps, which never leave the half-space x ≥ 0 (type a in x) and
return to the origin (x = 0 by type a, y = 0 and z = 0 by type b). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin (2 * n) → Fin 6 =>
    (∀ t ≤ 2 * n, 0 ≤ (pt w t).1) ∧ pt w (2 * n) = 0)).card

/-- Mathar's conjectured recurrence. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) ^ 3 * (a n : ℤ) -
      2 * (2 * (n : ℤ) - 1) * (10 * (n : ℤ) ^ 2 + 10 * (n : ℤ) + 3) * (a (n - 1) : ℤ) +
      36 * (n : ℤ) * (2 * (n : ℤ) - 1) * (2 * (n : ℤ) - 3) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a302181
