import Mathlib

/-!
# Erdős's squares-in-a-square problem (Erdős Problem 106)

Source: https://www.erdosproblems.com/106 (Paul Erdős; [ErGr75b], [Er94b], [Er95])
Listed on the desk as https://lefttosolve.com/p/aist-erdos-squares-in-a-square

Draw `n` squares inside the unit square with no common interior point, and let `f n` be the
maximum possible sum of the side lengths of the `n` squares. The problem asks

  `f (k ^ 2 + 1) = k` for every `k ≥ 1`?

The squares are arbitrary squares of the plane: tilted squares are allowed. The source
contrasts `f` with the variant `g`, defined identically except that every square has its
sides parallel to the sides of the unit square, and Baek, Koizumi and Ueoro settled `g`.
Only interiors have to be disjoint, so the squares may share boundary points, and squares of
side length `0` are admitted (they change no value of `f`).

Known, and not in question here: `f (k ^ 2) = k` by Cauchy-Schwarz, and `f (k ^ 2 + 1) ≥ k`
by cutting one of the `k ^ 2` small squares of side `1 / k` into two of side `1 / (2 * k)`;
`f 2 = 1` (Erdős) and `f 5 = 2` (Newman) are the cases `k = 1, 2`. The general question is
open. This file only states it; it proves nothing.
-/

namespace OMA.S_aist_erdos_squares_in_a_square

/-- The point of the plane with square coordinates `(u, v)` in the square of side length `s`
whose centre is `c` and whose sides are rotated by the angle `θ`. -/
noncomputable def sqPoint (c : ℝ × ℝ) (s θ u v : ℝ) : ℝ × ℝ :=
  (c.1 + s * (u * Real.cos θ - v * Real.sin θ),
   c.2 + s * (u * Real.sin θ + v * Real.cos θ))

/-- The closed square of side length `s`, centre `c`, rotated by the angle `θ`: the image of
`[0,1] × [0,1]` under `sqPoint c s θ`. -/
def square (c : ℝ × ℝ) (s θ : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ u ∈ Set.Icc (0 : ℝ) 1, ∃ v ∈ Set.Icc (0 : ℝ) 1, p = sqPoint c s θ u v}

/-- The interior of that square: the image of the open square `(0,1) × (0,1)`. -/
def squareInterior (c : ℝ × ℝ) (s θ : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ u ∈ Set.Ioo (0 : ℝ) 1, ∃ v ∈ Set.Ioo (0 : ℝ) 1, p = sqPoint c s θ u v}

/-- The closed unit square `[0,1] × [0,1]`. -/
def unitSquare : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1}

/-- `n` squares of nonnegative side length, all inside the unit square, with pairwise disjoint
interiors: a drawing of `n` squares in the unit square with no common interior point. -/
def IsPacking (n : ℕ) (c : Fin n → ℝ × ℝ) (s θ : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ s i) ∧
  (∀ i, square (c i) (s i) (θ i) ⊆ unitSquare) ∧
  (∀ i j, i ≠ j →
    Disjoint (squareInterior (c i) (s i) (θ i)) (squareInterior (c j) (s j) (θ j)))

/-- `f n`, the maximum possible sum of the side lengths of `n` squares drawn in the unit
square with pairwise disjoint interiors, written as the supremum of the achievable totals. -/
noncomputable def f (n : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ (c : Fin n → ℝ × ℝ) (s θ : Fin n → ℝ), IsPacking n c s θ ∧ t = ∑ i, s i}

/-- Erdős's question: is the maximum total side length of `k ^ 2 + 1` squares drawn in the
unit square with disjoint interiors equal to `k`, for every `k ≥ 1`? -/
theorem main : ∀ k : ℕ, 1 ≤ k → f (k ^ 2 + 1) = (k : ℝ) := by
  sorry

end OMA.S_aist_erdos_squares_in_a_square
