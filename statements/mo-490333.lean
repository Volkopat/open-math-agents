import Mathlib

/-!
# Taylor interpolation by finite Blaschke products at the boundary

MathOverflow 490333, “Approximation by Blaschke products in Carathéodory's theorem”.
https://mathoverflow.net/questions/490333
Credit: @pmaster

We use the equivalent rational-inner characterization of a finite Blaschke product.
Boundary values of the Schur function are its continuous extension across the arc.
The Taylor interpolation conditions in the question specify no terminal phase.
-/

open Filter Set
open scoped Topology

namespace OMA.S_mo_490333

/-- A rational inner function on the closed unit disk of degree at most n. -/
def IsBlaschkeAtMost (n : ℕ) (b : ℂ → ℂ) : Prop :=
  ∃ P Q : Polynomial ℂ, P.natDegree ≤ n ∧ Q.natDegree ≤ n ∧
    (∀ z, ‖z‖ ≤ 1 → Q.eval z ≠ 0 ∧ b z = P.eval z / Q.eval z) ∧
    ∀ z, ‖z‖ = 1 → ‖b z‖ = 1

/-- Whether Taylor interpolation through order n-1 always gives locally uniform
convergence up to an open arc of unimodularity. -/
theorem main : ∀ (f : ℂ → ℂ) (V : Set ℂ) (B : ℕ → ℂ → ℂ),
    IsOpen V →
    (∀ z, ‖z‖ < 1 → AnalyticAt ℂ f z ∧ ‖f z‖ ≤ 1) →
    (∀ z ∈ V, ‖z‖ = 1 → ContinuousWithinAt f (Metric.closedBall 0 1) z ∧ ‖f z‖ = 1) →
    (∀ n, IsBlaschkeAtMost n (B n)) →
    (∀ n j, j < n → iteratedDeriv j (B n) 0 = iteratedDeriv j f 0) →
    ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.closedBall 0 1 →
      (∀ z ∈ K, ‖z‖ = 1 → z ∈ V) → TendstoUniformlyOn B f atTop K := by
  sorry

end OMA.S_mo_490333
