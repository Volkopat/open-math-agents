import Mathlib

/-!
# The recursive ordinary generating function in OEIS A195068

Paul D. Hanna defines A(x) by A(x) = Σ_{r≥0} x^r A(r x)^r.
For a positive degree n, a summand with 1 ≤ r ≤ n assigns nonnegative
degrees to its r ordered factors. Those degrees sum to n-r. Substitution
of r*x multiplies the contribution by r^(n-r). All the indices in the
product are strictly smaller than n, giving the finite recursion below.
The r=0 summand gives the constant coefficient 1.

Vaclav Kotesovec conjectured the sixth-root growth rate in August 2026.
Source: https://oeis.org/A195068
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a195068
open Filter Topology Finset

def allocations (total slots : ℕ) : Finset (Fin slots → Fin (total+1)) :=
  univ.filter (fun f => (∑ i, (f i:ℕ)) = total)

def term (n : ℕ) : ℕ :=
  if hn : n=0 then 1 else
    ∑ j ∈ range n, (j+1)^(n-(j+1)) *
      ∑ f ∈ allocations (n-(j+1)) (j+1), ∏ i : Fin (j+1), term (f i : ℕ)
termination_by n
decreasing_by all_goals have h := (f i).isLt; omega

theorem main :
    Tendsto (fun n : ℕ => (term n:ℝ)^(1/(n:ℝ)^2)) atTop (𝓝 ((3:ℝ)^((1:ℝ)/6))) := by
  sorry

end OMA.S_oeis_a195068
