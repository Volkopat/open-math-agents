import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Lattice

/-! Source: https://mathoverflow.net/questions/504014 -/

open Filter
open scoped BigOperators Topology

namespace OMA.S_mo_504014

/-- The greatest common divisor of the tail whose first index is n. -/
noncomputable def tailGcd (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  sSup {d : ℕ | ∀ k : ℕ, n ≤ k → d ∣ a k}

/-- The nonnegative signed sums of the first n terms. -/
def signedSums (a : ℕ → ℕ) (n : ℕ) : Set ℤ :=
  {x | 0 ≤ x ∧ ∃ e : ℕ → Bool,
    x = ∑ i ∈ Finset.range n, if e i then (a i : ℤ) else -(a i : ℤ)}

theorem main : ∀ a : ℕ → ℕ, (∀ n, 0 < a n) →
    Tendsto (fun n : ℕ => (a n : ℝ) / (2 : ℝ) ^ (n + 1)) atTop (𝓝 0) →
    (∃ L : ℝ, 0 < L ∧
      Tendsto (fun n : ℕ => (a n : ℝ) / (a (n + 1) : ℝ)) atTop (𝓝 L)) →
    ((∀ n, tailGcd a n = tailGcd a 0) ∨ 1 < tailGcd a 0) →
    ∀ᶠ n : ℕ in atTop,
      IsLeast (signedSums a n) (((∑ i ∈ Finset.range n, a i) % (2 * tailGcd a 0) : ℕ) : ℤ) := by
  sorry

end OMA.S_mo_504014
