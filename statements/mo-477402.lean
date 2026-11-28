import Mathlib

/-!
# Poisson binomial conjecture

Source: https://mathoverflow.net/questions/477402
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (MathOverflow): let `X = ∑ X_i`, `Y = ∑ Y_i` with independent `X_i ~ Bernoulli(p_i)`,
`Y_i ~ Bernoulli(q_i)`, `p, q ∈ [0,1]^n`, `p_i ≥ q_i`, `n` even, `γ = (1/n) ∑ (p_i - q_i)`, and
`X̄ ~ Binomial(n, 1/2 + γ/2)`, `Ȳ ~ Binomial(n, 1/2 - γ/2)`. Then
`max_{k ≥ 0} |P(X ≥ k) - P(Y ≥ k)| ≥ P(X̄ ≥ n/2) - P(Ȳ ≥ n/2)`.

Conventions:
* Distributions are written explicitly: `P(X ≥ k) = ∑_{S ⊆ [n], |S| ≥ k} ∏_{i ∈ S} p_i ∏_{i ∉ S}
  (1 - p_i)`, and binomial tails `∑_{j ≥ k} C(n, j) r^j (1-r)^{n-j}`. The maximum over `k` is
  over `0 ≤ k ≤ n + 1` (other `k` give `0`). `n ≥ 2` even (for `n = 0` both sides vanish).
-/

namespace OMA.S_mo_477402

/-- `P(∑ X_i ≥ k)` for independent Bernoulli(`p_i`). -/
noncomputable def tail {n : ℕ} (p : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => k ≤ S.card),
    (∏ i ∈ S, p i) * ∏ i ∈ Sᶜ, (1 - p i)

/-- `P(Binomial(n, r) ≥ k)`. -/
noncomputable def binTail (n : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc k n, (n.choose j : ℝ) * r ^ j * (1 - r) ^ (n - j)

theorem main :
    ∀ (n : ℕ) (p q : Fin n → ℝ), 2 ≤ n → Even n →
      (∀ i, 0 ≤ q i ∧ q i ≤ p i ∧ p i ≤ 1) →
      let γ := (∑ i, (p i - q i)) / n
      ∃ k ∈ Finset.range (n + 2),
        binTail n (1 / 2 + γ / 2) (n / 2) - binTail n (1 / 2 - γ / 2) (n / 2) ≤
          |tail p k - tail q k| := by
  sorry

end OMA.S_mo_477402
