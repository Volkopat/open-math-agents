import Mathlib

/-!
# Mean number of divisors whose one-bits occur in the dividend

Source: https://oeis.org/A246600. The asymptotic-mean conjecture is due to
Amiram Eldar (2023). The term with d=n is included.
-/
namespace OMA.S_oeis_a246600
open Filter Topology

def term (n : ℕ) : ℕ := (n.divisors.filter (fun d => d &&& n = d)).card

noncomputable def weight (d : ℕ) : ℝ :=
  1 / ((d : ℝ) * 2^d.bitIndices.length)

theorem main : Summable (fun k : ℕ => weight (k+1)) ∧
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (term (k+1) : ℝ)) / N)
      atTop (𝓝 (1 + ∑' k : ℕ, weight (k+1))) := by
  sorry

end OMA.S_oeis_a246600
