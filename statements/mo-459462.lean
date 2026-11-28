import Mathlib

/-!
# The ratio of 2-associated to ordinary Stirling numbers

Source: János Engländer, https://mathoverflow.net/questions/459462 (CC BY-SA 4.0).
Credit: @connoranderson.

The coefficient of the k-th power of the block series, multiplied by n!/k!,
counts partitions of n labels into k blocks of size at least s. This is the
labelled product formula, with k! removing the ordering of the blocks.
We give the full strictness range, since both ratios are zero once 2k>n.
-/

namespace OMA.S_mo_459462
open PowerSeries
noncomputable section

def blocks (s : ℕ) : PowerSeries ℚ :=
  mk (fun j => if s ≤ j then (j.factorial:ℚ)⁻¹ else 0)

def associated (s n k : ℕ) : ℚ :=
  (n.factorial:ℚ)/(k.factorial:ℚ) * coeff n ((blocks s)^k)

def ratio (n k : ℕ) : ℚ := associated 2 n k / (Nat.stirlingSecond n k:ℚ)

theorem main : (∀ n k : ℕ, associated 1 n k=(Nat.stirlingSecond n k:ℚ)) ∧
    ∀ n k : ℕ, 2 ≤ n → 0 < k → k < n →
      (ratio n (k+1) ≤ ratio n k ∧ (ratio n (k+1) < ratio n k ↔ 2*k ≤ n) ∧
       (n < 2*k → ratio n k=0)) := by
  sorry

end
end OMA.S_mo_459462
