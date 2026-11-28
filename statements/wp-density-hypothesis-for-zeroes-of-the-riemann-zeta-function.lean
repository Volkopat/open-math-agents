import Mathlib

/-!
# Density hypothesis for zeroes of the Riemann zeta function.

Source: https://en.wikipedia.org/wiki/Bombieri–Vinogradov_theorem
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The cited page only mentions the density hypothesis; Wikipedia's "Density hypothesis" redirects to
"Lindelöf hypothesis" § "The density hypothesis", which states: N(σ, T) ≤ T^{2(1−σ)+ε} where
N(σ, T) is the number of zeros ρ of ζ(s) with ℜ(s) ≥ σ and |ℑ(s)| ≤ T. The O_ε reading unfolds to
∀ ε > 0 ∃ C > 0 ∀ σ T, 1/2 ≤ σ ≤ 1, T ≥ 2: N(σ, T) ≤ C · T^{2(1−σ)+ε}, matching the repo's
canonical formalization of this Wikipedia statement (FormalConjectures/Wikipedia/DensityHypothesis).
-/

namespace OMA.S_wp_density_hypothesis_for_zeroes_of_the_riemann_zeta_function

-- definitions the statement needs (no sorry, no axiom)

/-- Multiplicity-weighted count N(σ, T) of the zeros ρ = β + iγ of the Riemann zeta function
with σ ≤ β ≤ 1 and 0 < γ ≤ T, each zero counted with its analytic order (multiplicity).
Classical sources often count |γ| ≤ T; by conjugate symmetry of ζ and nonvanishing on the real
interval [1/2, 1], the two conventions differ only by a factor of 2, leaving O_ε bounds unchanged.
-/
noncomputable abbrev zetaZeroCount (σ T : ℝ) : ℕ :=
  ∑ᶠ s ∈ {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T},
    analyticOrderNatAt riemannZeta s

/-- Density Hypothesis: for every ε > 0 there exists C > 0 such that
N(σ, T) ≤ C · T^{2(1−σ)+ε} for all 1/2 ≤ σ ≤ 1 and T ≥ 2. -/
theorem main :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
        (zetaZeroCount σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) := by
  sorry

end OMA.S_wp_density_hypothesis_for_zeroes_of_the_riemann_zeta_function
