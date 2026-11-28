import Mathlib

/-!
# The least binary mask whose occupied positions cover an interval of even sums

Positions start at one for the least significant bit. The pair of positions
may use the same bit twice. The original sequence begins at n = 1.
Source: https://oeis.org/A397185
Credit: @rleshner
-/

namespace OMA.S_oeis_a397185

def covers (n : ℕ) (bits : Finset ℕ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ n → ∃ i ∈ bits, ∃ j ∈ bits, (i+1)+(j+1)=2*t

noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ covers n m.bitIndices.toFinset}

theorem main : ∀ k : ℕ, 1 ≤ k → a (2*k) = 2*a (2*k-1)+1 := by
  sorry

end OMA.S_oeis_a397185
