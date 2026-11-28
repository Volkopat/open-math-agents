import Mathlib

/-!
# Partitions into two positive squares

A025426 counts the unordered pairs of positive squares with sum `n`, allowing repetition.
Václav Kotešovec conjectured the partial-sum asymptotic on December 28, 2023.
Source: https://oeis.org/A025426 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a025426

/-- Each point `(i,j)` represents the strictly positive square roots `i+1` and `j+1`. -/
def quadrant (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range n.sqrt) ×ˢ (Finset.range n.sqrt)).filter
    (fun p => (p.1+1)^2 + (p.2+1)^2 ≤ n)

/-- The ordered choice of roots represents each unordered pair exactly once. -/
def triangle (n : ℕ) : Finset (ℕ × ℕ) := (quadrant n).filter (fun p => p.1 ≤ p.2)

/-- Number of partitions of `n` into two nonzero squares. -/
def a (n : ℕ) : ℕ := ((triangle n).filter (fun p => (p.1+1)^2 + (p.2+1)^2 = n)).card

theorem main :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => ((∑ k ∈ Finset.Icc 1 n, a k : ℕ) : ℝ))
      (fun n : ℕ => (n : ℝ) * Real.pi / 8) := by
  sorry

end OMA.S_oeis_a025426
