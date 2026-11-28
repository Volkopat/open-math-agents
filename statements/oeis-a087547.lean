import Mathlib

/-!
# A087547: Bala's finite sum for the integral sequence

Source: https://oeis.org/A087547

Peter Bala conjectured the factorial sum. It was proved by Sela Fried and
Toufik Mansour (arXiv:2304.05728). The left side uses the integral defining
A087547. The sum uses i = k - 1 for Bala's original index k.
-/

namespace OMA.S_oeis_a087547

noncomputable def a (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * 2^(n+1) *
    (∫ x : ℝ in (0 : ℝ)..1, 1 / (1 + x^2)^(n+1)) -
  Real.pi * ((2*n).factorial : ℝ) / (2^(n+1) * n.factorial)

theorem main : ∀ n : ℕ, a (n+1) =
    ∑ i ∈ Finset.range (n+1), (2:ℝ)^i * i.factorial * (n+i+1).factorial / (2*i+1).factorial := by
  sorry

end OMA.S_oeis_a087547
