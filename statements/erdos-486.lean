import Mathlib

/-!
# Erdős Problem 486

Does avoiding the prescribed residue classes for every smaller modulus always
give a set with logarithmic density? See https://www.erdosproblems.com/486.
-/

namespace OMA.S_erdos_486

open Filter
open scoped Topology

/-- The integers avoiding the forbidden residue classes for all smaller moduli in `A`. -/
def siftedSet (A : Set ℕ+) (X : (n : A) → Set (ZMod (n.1 : ℕ))) : Set ℕ :=
  {m | ∀ n : A, (n.1 : ℕ) < m → (m : ZMod (n.1 : ℕ)) ∉ X n}

/-- For a real cutoff `x`, the positive integers below `x` are precisely those
in the half-open interval from one to its natural ceiling. -/
theorem main : ∀ (A : Set ℕ+) (X : (n : A) → Set (ZMod (n.1 : ℕ))),
    ∃ d : ℝ, Tendsto (fun x : ℝ => (1 / Real.log x) *
      ∑ m ∈ Finset.Ico 1 ⌈x⌉₊, (siftedSet A X).indicator (fun k : ℕ => (k : ℝ)⁻¹) m)
      atTop (𝓝 d) := by
  sorry

end OMA.S_erdos_486

