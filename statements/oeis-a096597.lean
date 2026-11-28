import Mathlib

/-!
# A096597: Plane partitions of n whose 3D Ferrers plot just fits inside an m x m x m box

Source: https://oeis.org/A096597
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Triangle read by rows: T(n, m) = number of plane partitions of n whose 3-dimensional
Ferrers plot just fits inside an m x m x m box.
Conjecture: The last floor(n/2) terms of each row read backwards are 3*A091360
(three times the partial sums of A000219, the number of plane partitions).
-/

namespace OMA.S_oeis_a096597

def IsPlanePartition (n : ℕ) (π : ℕ × ℕ → ℕ) : Prop :=
  (∀ i j, (n ≤ i ∨ n ≤ j) → π (i, j) = 0) ∧
  (∀ i₁ i₂ j₁ j₂, i₁ ≤ i₂ → j₁ ≤ j₂ → π (i₂, j₂) ≤ π (i₁, j₁)) ∧
  (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, π (i, j)) = n

def FitsInBox (m : ℕ) (π : ℕ × ℕ → ℕ) : Prop :=
  (∀ i j, π (i, j) ≤ m) ∧
  (∀ i j, (m ≤ i ∨ m ≤ j) → π (i, j) = 0)

noncomputable def numPlanePartitions (n : ℕ) : ℕ :=
  Set.ncard {π : ℕ × ℕ → ℕ | IsPlanePartition n π}

noncomputable def T (n m : ℕ) : ℕ :=
  Set.ncard {π : ℕ × ℕ → ℕ | IsPlanePartition n π ∧ FitsInBox m π ∧ ¬ FitsInBox (m - 1) π}

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, k < n / 2 →
      T n (n - k) = 3 * ∑ j ∈ Finset.range (k + 1), numPlanePartitions j := by
  sorry

end OMA.S_oeis_a096597
