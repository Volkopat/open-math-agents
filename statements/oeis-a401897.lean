import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat

/-!
# OEIS A401897

Source: https://oeis.org/A401897 (Karan Sharma)

The observer is a nonzero lattice point in the sector 0 ≤ b ≤ a. Its
one-based index counts all sector points of smaller norm and the points
of equal norm with second coordinate at most b. The disk is open and
visibility is relative primality of the coordinate differences.
-/

namespace OMA.S_oeis_a401897

def sector (z : ℕ × ℕ) : Prop := 0 < z.1 ∧ z.2 ≤ z.1

def normSq (z : ℕ × ℕ) := z.1 ^ 2 + z.2 ^ 2

def rank (z : ℕ × ℕ) : ℕ :=
  ((Finset.range (normSq z + 1) ×ˢ Finset.range (normSq z + 1)).filter
    (fun w => 0 < w.1 ∧ w.2 ≤ w.1 ∧ (normSq w < normSq z ∨
      (normSq w = normSq z ∧ w.2 ≤ z.2)))).card

noncomputable def visible (z : ℕ × ℕ) : ℕ :=
  let r : ℤ := normSq z
  ((Finset.Icc (-r) r ×ˢ Finset.Icc (-r) r).filter (fun w =>
    w.1 ^ 2 + w.2 ^ 2 < r ∧
      Nat.Coprime (w.1 - (z.1 : ℤ)).natAbs (w.2 - (z.2 : ℤ)).natAbs)).card

theorem main : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ z : ℕ × ℕ,
    sector z → N ≤ rank z →
    |(visible z : ℝ) / (48 * (rank z : ℝ) / Real.pi ^ 2) - 1| < ε := by
  sorry

end OMA.S_oeis_a401897
