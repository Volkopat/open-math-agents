import Mathlib

/-!
# A247335: The curvature of touching circles inscribed in a special way in the larger segment of circle of radius 10/9 divided by a chord of length 4/3.

Source: https://oeis.org/A247335
Credit: @Salofe

The sequence is due to Kival Ngaokrajang (Sep 18 2014). Its first comment, quoted verbatim:
"Refer to comment of A092387. Consider a circle C of radius 10/9 (in some length units) with a
chord of length 4/3. This has been chosen such that the larger sagitta has length 2. The smaller
sagitta has length 2/9. The input, besides the circle C is the circle C_0 with radius R_0 = 1,
touching the chord and circle C. The following sequence of circles C_n with radii R_n, n >= 1, is
obtained from the conditions that C_n touches (i) the circle C, (ii) the chord and (iii) the
circle C_(n-1). The curvature of the n-th circle, C_n = 1/R_n, n >= 0, is conjectured to be a(n).
If one considers the curvature of touching circles inscribed in the smaller segment, the sequence
would be A247512. See an illustration given in the link."

Conjectures from Colin Barker, Sep 18 2014, quoted verbatim from the entry:
* "a(n) = 39*a(n-1) - 39*a(n-2) + a(n-3)."
* "G.f.: -(10*x^2-29*x+1) / ((x-1)*(x^2-38*x+1))."
(W. Lang, Sep 30 2014, gives proofs of these formulas in a note linked from the entry.)

The statement below says that the curvatures 1/R_n of the circles of the chain satisfy both of
Barker's formulas; the g.f. determines every term, so it also says that the curvature of the n-th
circle is the n-th term 1, 10, 361, 13690, ... of the data, as the comment conjectures. It also
says that such a chain exists. (The entry's second comment, on A078986 and A097315, is not part
of this statement.)

Formalization notes:
* Coordinates. A circle of radius 10/9 with a chord of length 4/3 is unique up to congruence,
  and congruences preserve tangency and radii. We fix C with center (0, 8/9) and radius 10/9, and
  the chord on the line y = 0 from (-2/3, 0) to (2/3, 0): (2/3)^2 + (8/9)^2 = (10/9)^2. The larger
  segment is the part of the disk with y ≥ 0 (sagitta 8/9 + 10/9 = 2; the smaller segment has
  sagitta 10/9 - 8/9 = 2/9, as in the entry).
* The circle C_n has center (u n, v n) and radius R n > 0, for every n ≥ 0 (offset 0), and
  R 0 = 1.
* `Inscribed`: C_n lies in the larger segment, touches the chord and touches C. Touching the
  chord from the side of the larger segment means being tangent to the line y = 0 from above,
  v n = R n, at the point (u n, 0), which must lie on the chord: -2/3 ≤ u n ≤ 2/3. Touching C
  from inside means that the distance of the centers is 10/9 - R n: R n ≤ 10/9 and
  u n ^ 2 + (v n - 8/9) ^ 2 = (10/9 - R n) ^ 2. These conditions say exactly that the closed disk
  of C_n lies in the closed larger segment and touches both the chord and C. The title's
  "inscribed in the larger segment" applies to every circle, C_0 included (C_0 is then forced to
  have center (0, 1)).
* `Touch`: C_(n+1) touches C_n, i.e. the two circles are different and tangent, externally
  (distance of the centers R n + R (n+1)) or internally (distance |R n - R (n+1)|); distances
  are compared through their squares. (For two circles of the chain only external tangency can
  occur, but internal tangency is not excluded by hypothesis.)
* The chain goes on: C_(n+2) differs from C_n. Given C_(n+1), exactly two circles satisfy (i),
  (ii) and (iii), namely C_n and the next circle of the chain; without this condition the
  sequence could go back and forth between two circles. For n = 0 there are two choices for C_1,
  mirror images of each other, with the same radius.
* a(n) is the curvature 1/R n. Barker's recurrence is stated for n ≥ 3 (it uses a(n-3)). The
  g.f. is the ordinary one, Sum_{n>=0} a(n) x^n, stated as an identity of formal power series
  over ℝ with the denominator (x-1)(x^2-38x+1) cleared; this denominator has constant
  coefficient -1, so the identity determines all coefficients.
* Faithfulness check: solving the conditions below exactly (sympy) step by step from R 0 = 1,
  branching over every solution, gives exactly two chains up to n = 6, mirror images under
  x ↦ -x, both with curvatures 1, 10, 361, 13690, 519841, 19740250, 749609641, the first terms
  of the data. Without the condition that C_(n+2) differs from C_n, chains such as 1, 10, 1, 10
  appear. The recurrence and the g.f. agree with all 601 terms of the b-file (n = 0..600).
-/

namespace OMA.S_oeis_a247335

open PowerSeries

/-- The circle with center `(x, y)` and radius `r > 0` lies in the larger segment of the circle
`C` (center `(0, 8/9)`, radius `10/9`) cut off by the chord from `(-2/3, 0)` to `(2/3, 0)`,
touches the chord (it is tangent to the line `y = 0` from above, at the point `(x, 0)` of the
chord) and touches `C` (internally: the distance of the centers is `10/9 - r`). -/
def Inscribed (x y r : ℝ) : Prop :=
  0 < r ∧ y = r ∧ -2/3 ≤ x ∧ x ≤ 2/3 ∧ r ≤ 10/9 ∧ x ^ 2 + (y - 8/9) ^ 2 = (10/9 - r) ^ 2

/-- The circles with center `(x, y)`, radius `r` and with center `(x', y')`, radius `r'` touch:
they are different, and tangent externally (distance of the centers `r + r'`) or internally
(distance of the centers `|r - r'|`). -/
def Touch (x y r x' y' r' : ℝ) : Prop :=
  (x', y', r') ≠ (x, y, r) ∧
    ((x' - x) ^ 2 + (y' - y) ^ 2 = (r + r') ^ 2 ∨ (x' - x) ^ 2 + (y' - y) ^ 2 = (r - r') ^ 2)

/-- The circles `C_n` (center `(u n, v n)`, radius `R n`, `n ≥ 0`) form the chain of the entry:
every `C_n` is inscribed in the larger segment touching the chord and `C`, `R 0 = 1`, each
`C_(n+1)` touches `C_n`, and the chain goes on (`C_(n+2)` is not `C_n` again). -/
def IsChain (u v R : ℕ → ℝ) : Prop :=
  (∀ n, Inscribed (u n) (v n) (R n)) ∧ R 0 = 1 ∧
    (∀ n, Touch (u n) (v n) (R n) (u (n + 1)) (v (n + 1)) (R (n + 1))) ∧
    (∀ n, (u (n + 2), v (n + 2), R (n + 2)) ≠ (u n, v n, R n))

/-- Such a chain exists, and for every such chain the curvatures `a(n) = 1/R n` satisfy Barker's
recurrence `a(n) = 39*a(n-1) - 39*a(n-2) + a(n-3)` (n ≥ 3) and have the generating function
`-(10x^2 - 29x + 1)/((x - 1)(x^2 - 38x + 1))`. -/
theorem main :
    (∃ u v R : ℕ → ℝ, IsChain u v R) ∧
    ∀ u v R : ℕ → ℝ, IsChain u v R →
      (∀ n, 3 ≤ n → 1 / R n = 39 * (1 / R (n - 1)) - 39 * (1 / R (n - 2)) + 1 / R (n - 3)) ∧
      PowerSeries.mk (fun n => 1 / R n) * ((X - 1) * (X ^ 2 - 38 * X + 1)) =
        -(10 * X ^ 2 - 29 * X + 1) := by
  sorry

end OMA.S_oeis_a247335
