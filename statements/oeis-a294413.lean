import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The golden-ratio limit in A294413

Source: https://oeis.org/A294413
Credit: @blakestone-x

The two increasing sequences partition the positive integers. The recurrence
is written over the integers to keep the negative term signed.
-/

namespace OMA.S_oeis_a294413

structure Solution (a b : ℕ → ℕ) : Prop where
  a_zero : a 0 = 1
  a_one : a 1 = 3
  b_zero : b 0 = 2
  b_one : b 1 = 4
  strict_a : StrictMono a
  strict_b : StrictMono b
  disjoint : ∀ i j, a i ≠ b j
  cover : ∀ m, 0 < m → (∃ i, a i = m) ∨ (∃ j, b j = m)
  recurrence : ∀ n, (a (n + 2) : ℤ) =
    a (n + 1) + a n - b (n + 1) + 6

theorem main : ∀ a b : ℕ → ℕ, Solution a b →
    Filter.Tendsto (fun n : ℕ => (a (n+1) : ℝ) / (a n : ℝ))
      Filter.atTop (nhds ((1 + Real.sqrt 5) / 2)) := by
  sorry

end OMA.S_oeis_a294413
