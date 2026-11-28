import Mathlib

/-!
# Squarefree square pyramidal numbers

Amiram Eldar's conjecture in OEIS A119356. A206256 is the Euler product
of 1−3/p² over the primes. The increasing-cutoff product is included to
specify this constant directly.
-/
namespace OMA.S_oeis_a119356
open Filter Topology Finset

def pyramidal (n : ℕ) := ∑ j ∈ range (n+1), j^2

noncomputable def frequency (N : ℕ) : ℝ := by
  classical
  exact (((range N).filter (fun n=>Squarefree (pyramidal n))).card : ℝ)/N

noncomputable def euler (B : ℕ) : ℝ :=
  ∏ p ∈ (range (B+1)).filter Nat.Prime, (1-3/(p:ℝ)^2)

theorem main : ∃ C : ℝ, 0<C ∧ Tendsto euler atTop (𝓝 C) ∧
    Tendsto frequency atTop (𝓝 (4*C)) := by
  sorry

end OMA.S_oeis_a119356
