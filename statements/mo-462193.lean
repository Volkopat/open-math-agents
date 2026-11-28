import Mathlib

/-!
# A trace bound for time reversal of a Markov chain

Source: Alex Damian, https://mathoverflow.net/questions/462193 (CC BY-SA 4.0).
Sushant's counterexample https://mathoverflow.net/a/514262 uses a lazy directed cycle.
We use the same walk in growing dimensions. For a doubly stochastic transition
matrix the uniform distribution is stationary and its time reversal is the transpose.
At time seven quarters of the dimension the proposed lower bound fails by a
fixed factor for every sufficiently large dimension divisible by four.
Credit: @connoranderson.
-/

namespace OMA.S_mo_462193
open Filter Finset Matrix

noncomputable def reversal {α : Type} (P : Matrix α α ℝ) (π : α → ℝ) : Matrix α α ℝ :=
  Matrix.of (fun i j => P j i * π j / π i)

theorem main : ∀ (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (P : Matrix α α ℝ) (π : α → ℝ),
    (∀ i j, 0 ≤ P i j) → (∀ i, ∑ j, P i j = 1) →
    (∀ i, 0 < π i) → (∑ i, π i) = 1 → (∀ j, ∑ i, π i * P i j = π j) →
    ∀ k : ℕ, 0 < k → 1 ≤ (∑ i ∈ range k, (reversal P π * P^(i+1)).trace) / k := by
  sorry

end OMA.S_mo_462193
