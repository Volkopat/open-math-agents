import Mathlib

/-!
# A336431: Practical numbers and generalized polygonal numbers

Source: https://oeis.org/A336431
Conjectures: Zhi-Wei Sun (2020)
Credit: @Krgrocon
-/

namespace OMA.S_oeis_a336431

/-- All integers through a positive practical number are sums of distinct divisors. -/
def isPractical (t : ℕ) : Prop :=
  0 < t ∧ ∀ m : ℕ, m ≤ t → ∃ s : Finset ℕ, s ⊆ t.divisors ∧ m = ∑ i ∈ s, i

/-- The integer index uniquely determines the missing practical summand. -/
def heptagonalIndices (n : ℕ) : Set ℤ :=
  {k | ∃ t : ℕ, isPractical t ∧ (n : ℤ) = t + k * (5 * k - 3) / 2}

def singletons : Finset ℕ :=
  {1,3,4,7,10,11,14,18,23,26,27,44,51,53,65,68,77,80,92,125,143,170,179,182,
   185,191,206,296,362,383,425,437,674,1340,1622,2273,2558,3167,5591}

def conjectureOne : Prop :=
  ∀ n : ℕ, 0 < n →
    0 < (heptagonalIndices n).ncard ∧ ((heptagonalIndices n).ncard = 1 ↔ n ∈ singletons)

def conjectureTwo : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ t : ℕ, isPractical t ∧ ∃ k : ℤ, (n : ℤ) = t + k * (3 * k - 1) / 2

theorem main : conjectureOne ∧ conjectureTwo := by
  sorry

end OMA.S_oeis_a336431
