import Mathlib

/-!
# Is the Poisson binomial CDF decreasing in the success probabilities?

Source: https://mathoverflow.net/questions/275621
Credit: @koolkao

Question (Rakshith, MathOverflow 275621, 2017; CC BY-SA 3.0). Let `X = ∑_{i=1}^N X_i`, where
`X_i ∼ Bernoulli(p_i)`. Let `Y = ∑_{i=1}^N Y_i`, where `Y_i ∼ Bernoulli(p_i + δ)` for some
`0 ≤ δ ≤ 1 - max_i p_i`. All considered random variables are independent. Can we prove
`P(X ≤ k) ≥ P(Y ≤ k)` for all `k ∈ {0, …, N}`?

`main` states that the answer is yes. A disproof is a choice of `N`, `p`, `δ` and `k` with
`P(X ≤ k) < P(Y ≤ k)`.

Translation choices:
* the variables are indexed by `Fin N`; the law of independent `X_i ∼ Bernoulli(p_i)` is written
  out: the event that exactly the `X_i` with `i ∈ S` equal `1` has probability
  `(∏ i ∈ S, p i) * ∏ i ∈ Sᶜ, (1 - p i)`, and `P(X ≤ k)` is the sum of these over the sets `S`
  with `#S ≤ k` (`cdf p k`);
* the hypotheses are `0 ≤ p i`, `0 ≤ δ` and `p i + δ ≤ 1` for all `i` (that is,
  `δ ≤ 1 - max_i p_i`; then every `p i` and `p i + δ` is a probability).
-/

namespace OMA.S_mo_275621

/-- `P(X_1 + ⋯ + X_N ≤ k)` for independent `X_i ∼ Bernoulli(p i)`. -/
noncomputable def cdf {N : ℕ} (p : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card ≤ k),
    (∏ i ∈ S, p i) * ∏ i ∈ Sᶜ, (1 - p i)

/-- Raising every success probability by `δ` can only lower the Poisson binomial CDF. -/
theorem main :
    ∀ (N : ℕ) (p : Fin N → ℝ) (δ : ℝ), (∀ i, 0 ≤ p i) → 0 ≤ δ → (∀ i, p i + δ ≤ 1) →
      ∀ k : ℕ, k ≤ N → cdf (fun i => p i + δ) k ≤ cdf p k := by
  sorry

end OMA.S_mo_275621
