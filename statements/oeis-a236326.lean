import Mathlib

/-!
# A236326: a(n)*Pi is the total length of irregular spiral (center points: 1, 2, 3, 4, 5; pattern 1) after n rotations.

Source: https://oeis.org/A236326
Credit: @Salofe

Definition (comment of the entry): Let points 1, 2, 3, 4, and 5 be placed on a horizontal straight
line at intervals of 1 unit. Construct a continuous curve from half circles, alternately lying
below and above the line, centered at points 1, 2, 3, 4, 5, 1, ... and so on, with the first half
circle (centered at point 1) beginning at point 2.

The claims of the entry, as quoted by the problem:
* Conjecture: All forms of 120 permutations of 5 center points are non-expanded loops.
  (comment of the entry, which was created by Kival Ngaokrajang, Jan 22 2014)
* Conjectures from Colin Barker, Jul 12 2014: (Start)
  a(n) = a(n-1)+a(n-5)-a(n-6).
  G.f.: x*(7*x^4+7*x^3+4*x^2+3*x+3) / ((x-1)^2*(x^4+x^3+x^2+x+1)). (End)
* a(n) = 3*n + 4*floor(n/5) + 4*floor((n+1)/5) + floor((n+2)/5). In particular, Barker's
  conjectures are true (see Fried link). - Sela Fried, May 08 2026
The entry already says that Barker's conjectures are true (Sela Fried). This file states all of
the claims above as one conjunction.

Formalization notes:
* Point j sits at coordinate j (j = 1, ..., 5), so all start points, centers and radii are
  integers. A curve is given by the centers `c 0, c 1, c 2, ...` of its half circles and the start
  point `x₀` of the first one. Half circle k (counting from k = 0) begins at `startPt c x₀ k`, has
  center `c k` and radius `|startPt c x₀ k - c k|`, and ends at the mirror image
  `2 * c k - startPt c x₀ k` of its start point in its center, where half circle k + 1 begins
  (the curve is continuous). Half circle k lies below the line for even k and above it for odd k.
  A half circle of radius r has length r * Pi.
* A236326: half circle k is centered at point (k mod 5) + 1 (points 1, 2, 3, 4, 5, 1, ...) and the
  first one begins at point 2, so `x₀ = 2`. One rotation is two consecutive half circles, one below
  and one above the line (Fried: two consecutive half circles with nonzero radii; the program of
  the entry prints the running sum after every two nonzero radii). No radius of this curve is 0
  (the radii repeat with period 10 as 1, 2, 1, 2, 1, 3, 4, 3, 4, 3), so n rotations are the first
  2n half circles and a(n) is the sum of their radii, the total length divided by Pi. Offset 1;
  `a 0` is the empty sum 0 and is not a term. The definition gives the listed terms
  3, 6, 10, 17, 24, 27, 30, 34, ... (all 68 listed terms and the 10000 terms of the b-file were
  checked).
* Ngaokrajang's conjecture is about the same construction with the 5 center points taken in any
  of the 120 orders: for a permutation σ of {0, ..., 4}, half circle k is centered at point
  σ (k mod 5) + 1 (`permCenter σ k`; σ = 1 gives the centers of A236326). A non-expanded loop (as
  opposed to the expanded spiral of A235088, whose radii grow without bound) is read as: the curve
  closes up and repeats itself, that is, for some p > 0 every half circle k + p has the same start
  point, the same center and the same side of the line as half circle k (so the curve is bounded).
  The entry does not say where the first half circle begins when the points are permuted (its
  program starts 1 unit to the right of the first center for pattern 1, and 1 unit to the left of it
  for pattern 2, which is A236327, where the conjecture also appears); the statement allows every
  integer starting point `x₀`, which covers both patterns and any other reading.
* Barker's recurrence is stated for n ≥ 7, so that all of its indices are terms (≥ 1). His g.f. is
  stated as an identity of formal power series over ℚ for the series of a(n) x^n over n ≥ 1
  (coefficient 0 at x^0):
  (∑_{n ≥ 1} a(n) X^n) * ((X - 1)^2 * (X^4 + X^3 + X^2 + X + 1)) = X * (7X^4 + 7X^3 + 4X^2 + 3X + 3).
* Fried's formula is stated for n ≥ 1; floor((n + j)/5) is the natural-number quotient (n + j) / 5.
-/

namespace OMA.S_oeis_a236326

/-- `startPt c x₀ k` is the point where half circle k begins, for the curve whose half circles
are centered at `c 0, c 1, ...` and whose first half circle begins at `x₀`: each half circle ends
at the mirror image of its start point in its center, and the next one begins there. -/
def startPt (c : ℕ → ℤ) (x₀ : ℤ) : ℕ → ℤ
  | 0 => x₀
  | (k + 1) => 2 * c k - startPt c x₀ k

/-- A236326: half circle k is centered at point (k mod 5) + 1. -/
def center (k : ℕ) : ℤ := ((k % 5 : ℕ) : ℤ) + 1

/-- A236326: half circle k begins at `pos k`; the first one begins at point 2. -/
def pos (k : ℕ) : ℤ := startPt center 2 k

/-- A236326: the radius of half circle k. -/
def radius (k : ℕ) : ℤ := |pos k - center k|

/-- A236326 (offset 1): the total length of the first n rotations (2n half circles) divided by
Pi, that is, the sum of the first 2n radii. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (2 * n), radius k

/-- The centers for the order σ of the 5 center points: half circle k is centered at point
σ (k mod 5) + 1. -/
def permCenter (σ : Equiv.Perm (Fin 5)) (k : ℕ) : ℤ :=
  ((σ ⟨k % 5, Nat.mod_lt k (by norm_num)⟩ : ℕ) : ℤ) + 1

open PowerSeries in
/-- Ngaokrajang's conjecture, Barker's two conjectures, and Fried's formula. -/
theorem main :
    (∀ σ : Equiv.Perm (Fin 5), ∀ x₀ : ℤ, ∃ p : ℕ, 0 < p ∧ ∀ k : ℕ,
      startPt (permCenter σ) x₀ (k + p) = startPt (permCenter σ) x₀ k ∧
        permCenter σ (k + p) = permCenter σ k ∧ (k + p) % 2 = k % 2) ∧
    (∀ n : ℕ, 7 ≤ n → a n = a (n - 1) + a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((X - 1) ^ 2 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X * (7 * X ^ 4 + 7 * X ^ 3 + 4 * X ^ 2 + 3 * X + 3) ∧
    (∀ n : ℕ, 1 ≤ n →
      a n = 3 * (n : ℤ) + 4 * ((n / 5 : ℕ) : ℤ) + 4 * (((n + 1) / 5 : ℕ) : ℤ) +
        (((n + 2) / 5 : ℕ) : ℤ)) := by
  sorry

end OMA.S_oeis_a236326
