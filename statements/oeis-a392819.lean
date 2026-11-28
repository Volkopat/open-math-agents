import Mathlib

/-!
# OEIS A392819: natural density zero

Source: https://oeis.org/A392819

Felix Huber conjectured that the positive integers `n` such that
`p + v_p(n)` divides `n` for every prime divisor `p` have natural density zero.
Here `n.factorization p` is the exponent `v_p(n)`.
-/

open Filter
open scoped Topology

namespace OMA.S_oeis_a392819

/-- The divisibility condition defining the positive terms of A392819. -/
def isTerm (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p + n.factorization p ∣ n

/-- Number of terms in the interval from one to the cutoff, inclusive. -/
noncomputable def count (X : ℕ) : ℕ :=
  open Classical in ((Finset.Icc 1 X).filter isTerm).card

theorem main : Tendsto (fun X : ℕ => (count X : ℝ) / (X : ℝ)) atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a392819
