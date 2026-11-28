import Mathlib

/-!
# Inclusive depths in a null-balanced ternary tree

Cha's N(n) is the sum of the inclusive depths of the n nodes. All levels
before the last are full, so the choice of positions on the last level does
not affect the sum. We take the complete ternary tree in breadth-first order:
the root has index 0, and node i has children 3i+1, 3i+2 and 3i+3.

Sean A. Irvine conjectured that N is the partial sums of A064099, whose
offset is zero and whose terms are the ceiling of log base 3 of 3+2k.
The first term N(1) counts the root.

Sources: https://oeis.org/A213510 and https://oeis.org/A064099
Sung-Hyuk Cha (2012), https://naun.org/multimedia/UPress/ami/16-125.pdf
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a213510

def inclusiveDepth : (i : ℕ) → ℕ
  | 0 => 1
  | i+1 => inclusiveDepth (i/3) + 1
termination_by i => i

def depthSum (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, inclusiveDepth i

theorem main : ∀ n : ℕ, 0 < n →
    depthSum n = ∑ k ∈ Finset.range n, Nat.clog 3 (3+2*k) := by
  sorry

end OMA.S_oeis_a213510
