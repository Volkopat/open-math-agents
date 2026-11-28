import Mathlib

/-!
# A166212: Number of 4 X 4 X 4 triangular nonnegative integer arrays, symmetric under 120 degree rotation, with all sums of an element and its neighbors <= n

Source: https://oeis.org/A166212
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-28.
Offset 0 (data 1, 3, 6, 14, 25, 39, 66, 99, 138, 201, ...).

Conventions:
* A 4 X 4 X 4 triangular array has 10 cells indexed by barycentric coordinates
  `Cell = { p : Fin 4 × Fin 4 × Fin 4 // (p.1 : ℕ) + (p.2.1 : ℕ) + (p.2.2 : ℕ) = 3 }`.
* The 120-degree rotation sends `(a, b, c)` to `(b, c, a)`.
* Two cells are neighbors on the triangular grid iff their L1 distance in barycentric
  coordinates equals 2 (one coordinate agrees and the other two differ by 1 in opposite
  directions).
* Every entry is a nonnegative integer bounded by `n` (since the sum of each entry and its
  neighbors is at most `n`), so arrays are encoded as `f : Cell → Fin (n + 1)`.
* The generating function is stated after multiplication by its denominator, whose constant
  term is one.

Conjectures from Colin Barker, Feb 26 2018: (Start)
G.f.: (1 + x + x^2 + 3*x^3 + x^4 + x^5 + 3*x^6) / ((1 - x)^5*(1 + x)*(1 - x + x^2)*(1 + x + x^2)^3).
a(n) = 2*a(n-1) - a(n-2) + 2*a(n-3) - 4*a(n-4) + 2*a(n-5) - 2*a(n-9) + 4*a(n-10) - 2*a(n-11) + a(n-12) - 2*a(n-13) + a(n-14) for n>13.
(End)
-/

namespace OMA.S_oeis_a166212

open PowerSeries

/-- The 10 cells of a 4 X 4 X 4 triangular array in barycentric coordinates. -/
abbrev Cell := { p : Fin 4 × Fin 4 × Fin 4 // (p.1 : ℕ) + (p.2.1 : ℕ) + (p.2.2 : ℕ) = 3 }

/-- 120-degree rotation of the triangular array. -/
def rot (p : Cell) : Cell :=
  ⟨(p.1.2.1, p.1.2.2, p.1.1), by have h := p.2; dsimp; omega⟩

/-- Two cells are adjacent in the triangular grid iff their L1 distance is 2. -/
def adj (p q : Cell) : Prop :=
  ((p.1.1 : ℤ) - q.1.1).natAbs + ((p.1.2.1 : ℤ) - q.1.2.1).natAbs +
    ((p.1.2.2 : ℤ) - q.1.2.2).natAbs = 2

instance (p q : Cell) : Decidable (adj p q) := by
  unfold adj
  infer_instance

/-- Sum of an element and its triangular-grid neighbors. -/
def nbrSum {n : ℕ} (f : Cell → Fin (n + 1)) (p : Cell) : ℕ :=
  ∑ q : Cell, if q = p ∨ adj p q then (f q : ℕ) else 0

/-- An array is valid for parameter `n` if it is 120-degree rotationally symmetric and
every element plus its neighbors sums to at most `n`. -/
def valid (n : ℕ) (f : Cell → Fin (n + 1)) : Prop :=
  (∀ p : Cell, f (rot p) = f p) ∧ (∀ p : Cell, nbrSum f p ≤ n)

instance (n : ℕ) (f : Cell → Fin (n + 1)) : Decidable (valid n f) := by
  unfold valid
  infer_instance

/-- A166212: number of 4 X 4 X 4 rotationally symmetric triangular nonnegative integer arrays
with all element-plus-neighbor sums at most `n`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (valid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) ^ 5 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) ^ 3) =
      1 + X + X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + 3 * X ^ 6) ∧
    (∀ n : ℕ, 13 < n →
      (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + 2 * a (n - 3) - 4 * a (n - 4) +
        2 * a (n - 5) - 2 * a (n - 9) + 4 * a (n - 10) - 2 * a (n - 11) +
        a (n - 12) - 2 * a (n - 13) + a (n - 14)) := by
  sorry

end OMA.S_oeis_a166212
