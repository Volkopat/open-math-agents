import Mathlib

namespace OMA.S_mo_280236

def rationalSequences : Set (ℕ → ℝ) :=
  {x | ∀ n, ∃ q : ℚ, (q : ℝ) = x n}

def eventuallyZeroRationalSequences : Set (ℕ → ℝ) :=
  {x | x ∈ rationalSequences ∧ ∃ N : ℕ, ∀ n ≥ N, x n = 0}

/-- Is there a continuous map on the countable product of real lines
whose rational-sequence preimage is exactly the eventually zero rational sequences? -/
theorem main :
    ∃ f : (ℕ → ℝ) → (ℕ → ℝ),
      Continuous f ∧ f ⁻¹' rationalSequences = eventuallyZeroRationalSequences := by
  sorry

end OMA.S_mo_280236
