import Mathlib

/-!
# The Laplace integral for semi-increasing binary plane trees

Source: https://oeis.org/A227917
Credit: @VestigeClub

The sequence counts labelled plane binary trees in which a vertex with two
children has a smaller label than each of its descendants. We use the finite
formula in unsigned Stirling numbers of the first kind recorded by Ilya
Gutkovskiy in 2021, independently of Velin Yanev's 2026 integral conjecture.
The entry starts at n = 1. The summand at k = 0 vanishes at every such n.
The finite product is the ordinary rising factorial of its real argument.
-/

namespace OMA.S_oeis_a227917

def trees (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n+1), Nat.stirlingFirst n k * k.factorial * 2^(n-k)

def rising (x : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, (x+(j:ℝ))

theorem main : ∀ n : ℕ, 1 ≤ n → (trees n : ℝ) =
    2^(n+1) * ∫ x in Set.Ioi (0:ℝ), rising x n / Real.exp (2*x) := by
  sorry

end OMA.S_oeis_a227917
