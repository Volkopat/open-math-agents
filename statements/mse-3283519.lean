import Mathlib

/-!
# Conjectured formula for the Fabius function

Source: https://math.stackexchange.com/questions/3283519
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The Fabius function is the unique `F : ℝ → [-1, 1]` with `F(x) = ∫_0^{2x} F(t) dt` and
`F(1) = 1`. Conjecture (asker): for all non-negative integers `m, n`, `F(m / 2ⁿ) = 𝓕ⁿₘ`, where
`𝓕ⁿₘ = 1 / (2^(n²) (1/2; 1/2)ₙ) · ∑_{k=0}^{n} [n choose k]_{1/2} / (2^(k(k-1)) (n+k)!)
  · ∑_{ℓ=0}^{2^k m - 1} (-1)^(s₂(ℓ)) (ℓ - 2^k m + 1/2)^(n+k)`,
`(a; q)ₙ = ∏_{j<n} (1 - a q^j)` is the q-Pochhammer symbol, `[n choose k]_q` the q-binomial
coefficient and `s₂(ℓ)` the binary digit sum.

Conventions:
* `main` quantifies over every `F` with the two defining properties (as in the source), so it
  does not rely on the uniqueness claim. `m > 2ⁿ` and even `m` are allowed, as in the source.
* All of `𝓕ⁿₘ` is computed in `ℚ`.
-/

namespace OMA.S_mse_3283519

/-- The q-Pochhammer symbol `(a; q)ₙ`. -/
def qPoch (a q : ℚ) (n : ℕ) : ℚ := ∏ j ∈ Finset.range n, (1 - a * q ^ j)

/-- The q-binomial coefficient `[n choose k]_q`. -/
def qBinom (q : ℚ) (n k : ℕ) : ℚ := qPoch q q n / (qPoch q q k * qPoch q q (n - k))

/-- Binary digit sum `s₂(ℓ)`. -/
def s2 (l : ℕ) : ℕ := (Nat.digits 2 l).sum

/-- The conjectured value `𝓕ⁿₘ`. -/
def calF (m n : ℕ) : ℚ :=
  1 / (2 ^ (n ^ 2) * qPoch (1 / 2) (1 / 2) n) *
    ∑ k ∈ Finset.range (n + 1), qBinom (1 / 2) n k / (2 ^ (k * (k - 1)) * (n + k).factorial) *
      ∑ l ∈ Finset.range (2 ^ k * m),
        (-1 : ℚ) ^ s2 l * ((l : ℚ) - 2 ^ k * m + 1 / 2) ^ (n + k)

/-- The Fabius function takes the values `𝓕ⁿₘ` at the dyadic rationals `m / 2ⁿ`. -/
theorem main : ∀ F : ℝ → ℝ, (∀ x, F x ∈ Set.Icc (-1 : ℝ) 1) →
    (∀ x, F x = ∫ t in (0 : ℝ)..(2 * x), F t) → F 1 = 1 →
    ∀ m n : ℕ, F ((m : ℝ) / 2 ^ n) = (calF m n : ℝ) := by
  sorry

end OMA.S_mse_3283519
