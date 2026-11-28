import Mathlib

/-!
# Zeros of reflected sums and differences of zeta derivatives

Source: https://mathoverflow.net/q/93323
Credit: @PastaPastaPasta
-/

namespace OMA.S_mo_93323

/-- For every positive derivative order, every nonreal zero of either signed
combination in the open critical strip has real part one half. -/
theorem main : ∀ k : ℕ, 0 < k → ∀ s : ℂ, 0 < s.re → s.re < 1 → s.im ≠ 0 →
    (iteratedDeriv k riemannZeta s + iteratedDeriv k riemannZeta (1 - s) = 0 ∨
     iteratedDeriv k riemannZeta s - iteratedDeriv k riemannZeta (1 - s) = 0) →
    s.re = 1 / 2 := by
  sorry

end OMA.S_mo_93323
