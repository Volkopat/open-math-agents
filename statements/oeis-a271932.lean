import Mathlib

namespace OMA.S_oeis_a271932

open PowerSeries BigOperators

/-- Composition `(F ∘ U)` of formal power series over `ℤ` when `coeff 0 U = 0`,
defined at degree `m` by the finite sum `∑_{k=0}^m (coeff k F) * coeff m (U ^ k)`. -/
noncomputable def compSeries (F U : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun m =>
    ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k F * PowerSeries.coeff m (U ^ k)

/-- OEIS A271932 general conjecture (special case `p = 7`):
"More generally, for prime p there exists an integer series G(x) that satisfies:
G(x) = G( x^p + p*x*G(x)^p )^(1/p) with G(0)=0, G'(0)=1 (conjecture)."
Equivalently, `G(x)^p = G(x^p + p*x*G(x)^p)` with `coeff 0 G = 0` and `coeff 1 G = 1`. -/
theorem main :
    ∀ p : ℕ, p.Prime →
      ∃ G : PowerSeries ℤ,
        PowerSeries.coeff 0 G = 0 ∧
        PowerSeries.coeff 1 G = 1 ∧
        G ^ p = compSeries G (PowerSeries.X ^ p + PowerSeries.C (p : ℤ) * PowerSeries.X * G ^ p) := by
  sorry

end OMA.S_oeis_a271932
