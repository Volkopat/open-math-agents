import Mathlib

/-!
# Talagrand's convolution conjecture on the hypercube (`L¹` regularization by the noise semigroup)

Source: https://arxiv.org/abs/1907.10896
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

N. Gozlan, X.-M. Li, M. Madiman, C. Roberto and P.-M. Samson, "Log-Hessian and deviation bounds for
Markov semi-groups, and regularization effect in `L¹`" (arXiv:1907.10896, Potential Anal. 2023).
Abstract: "Talagrand had conjectured in 1989 that the noise operator on the Boolean hypercube has a
further subtle regularization property for functions that are just integrable, but this conjecture
remains open." In the introduction: `Ωₙ = {-1, 1}ⁿ` with uniform measure `μₙ`, and `(P_s)_{s ≥ 0}` the
semigroup of `Lf(σ) = ½ ∑ᵢ (f(σⁱ) - f(σ))` ("convolution by a biased coin"), given by
`P_s f(σ) = ∫ f(η) ∏ᵢ (1 + e^{-s} σᵢ ηᵢ) dμₙ(η)`. With `𝓕ₙ` the nonnegative `f` with `‖f‖₁ = 1`,
Talagrand's Conjecture 1 states that for every `s > 0`,
  `lim_{t → ∞} t · sup_n sup_{f ∈ 𝓕ₙ} μₙ({σ : P_s f(σ) ≥ t}) = 0`,
and the stronger Conjecture 2 asks for the bound `c_s / √(log t)` (`t > 1`, `c_s` independent of `n`).
"Both conjectures are still open." (Markov's inequality only gives `t · μₙ(P_s f ≥ t) ≤ 1`; the
Gaussian analogue was proved by Eldan–Lee and Lehec.) This file states Conjecture 1, the
regularization property named in the abstract.

Modelling choices:
* `{-1, 1}ⁿ` is `Fin n → Bool` (`true` = `+1`), and `μₙ` is the normalized counting measure, so
  `∫ g dμₙ = 2⁻ⁿ ∑_σ g(σ)`.
* The limit statement is written in `ε`–`T` form: for every `ε > 0` there is `T` such that for all
  `t ≥ T`, all `n` and all `f ∈ 𝓕ₙ`, `t · μₙ(P_s f ≥ t) ≤ ε`. This is exactly
  `t · sup_n sup_f μₙ(P_s f ≥ t) → 0` (the quantity is nonnegative).
-/

namespace OMA.S_arxiv_1907_10896

/-- The coordinate `σᵢ ∈ {-1, 1}`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The noise semigroup `P_s f(σ) = 2⁻ⁿ ∑_η f(η) ∏ᵢ (1 + e^{-s} σᵢ ηᵢ)`. -/
noncomputable def P {n : ℕ} (s : ℝ) (f : (Fin n → Bool) → ℝ) (σ : Fin n → Bool) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ η : Fin n → Bool,
    f η * ∏ i, (1 + Real.exp (-s) * sgn (σ i) * sgn (η i))

/-- `μₙ({σ : P_s f(σ) ≥ t})`. -/
noncomputable def tailProb {n : ℕ} (s : ℝ) (f : (Fin n → Bool) → ℝ) (t : ℝ) : ℝ :=
  open Classical in
  (2 : ℝ) ^ (-(n : ℤ)) * ((Finset.univ.filter fun σ => t ≤ P s f σ).card : ℝ)

/-- **Talagrand's convolution conjecture (Conjecture 1).** -/
theorem main :
    ∀ s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), (∀ σ, 0 ≤ f σ) →
        (2 : ℝ) ^ (-(n : ℤ)) * ∑ σ, f σ = 1 →
          t * tailProb s f t ≤ ε := by
  sorry

end OMA.S_arxiv_1907_10896
