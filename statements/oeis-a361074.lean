import Mathlib

/-!
# Binary weights along the diagonals of A066884

Source: https://oeis.org/A361074. Václav Kotěšovec conjectured the asymptotic on
March 4, 2023. The sequence sums the j-th smallest integer of binary weight n-j+1
over 1 ≤ j ≤ n. In the sum below, i = j-1 because Nat.nth counts from zero.
Every weight used by this definition is positive.
Credit: @Aryan-Poonacha
-/

namespace OMA.S_oeis_a361074

/-- The zero-based i-th natural number with exactly k set bits. -/
noncomputable def weightEntry (k i : ℕ) : ℕ :=
  Nat.nth (fun x : ℕ => x.bitIndices.length = k) i

/-- The diagonal sum with a(0)=0, a(1)=1, a(2)=5, and a(3)=16. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, weightEntry (n-i) i

theorem main : Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (2 : ℝ)^n)
    Filter.atTop (nhds (19 / 6 : ℝ)) := by
  sorry

end OMA.S_oeis_a361074
