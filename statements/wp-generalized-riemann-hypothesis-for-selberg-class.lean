import Mathlib

/-!
# Generalized Riemann hypothesis for the Selberg class

Source: https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis#Generalized_Riemann_hypothesis_for_Selberg_class
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: do the nontrivial zeros of every function in the Selberg class lie on the critical
line `Re s = 1/2`? `main` states the positive answer (Selberg's conjecture).

Selberg class (Selberg's axioms). `F(s) = ∑_{n ≥ 1} a(n) n^{-s}` with
1. `a(1) = 1`, and the series converges absolutely for `Re s > 1`;
2. analyticity: for some `m`, `(s - 1)^m F(s)` extends to an entire function of finite order;
3. functional equation: `Φ(s) = Q^s ∏_{i<k} Γ(λ_i s + μ_i) F(s)` satisfies
   `Φ(s) = ω · conj(Φ(1 - conj s))` with `Q > 0`, `λ_i > 0`, `Re μ_i ≥ 0`, `|ω| = 1`;
4. Ramanujan: `a(n) = O(n^ε)` for every `ε > 0`;
5. Euler product: `log F(s) = ∑ b(n) n^{-s}` for `Re s > 1`, with `b(n) = 0` unless `n` is a
   prime power and `b(n) = O(n^θ)` for some `θ < 1/2`.

Encoding notes. `F : ℂ → ℂ` is the continuation (its value at `s = 1` is irrelevant). The
functional equation is imposed on the open strip `0 < Re s < 1`, where no Gamma factor has a
pole on either side; by analytic continuation this is equivalent to the full equation.
"Log F = ∑ b(n) n^{-s}" is written `F s = exp (∑ b(n) n^{-s})`. Nontrivial zeros are taken
to be the zeros in the open strip `0 < Re s < 1` (trivial zeros come from Gamma poles and lie
in `Re s ≤ 0`).
-/

namespace OMA.S_wp_generalized_riemann_hypothesis_for_selberg_class

open Complex

/-- `F` (with coefficients `a`) is in the Selberg class. -/
def InSelbergClass (a : ℕ → ℂ) (F : ℂ → ℂ) : Prop :=
  a 1 = 1 ∧
  (∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ F s = LSeries a s) ∧
  (∃ (m : ℕ) (G : ℂ → ℂ), Differentiable ℂ G ∧ (∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) ∧
    ∃ A C : ℝ, ∀ s, ‖G s‖ ≤ C * Real.exp (‖s‖ ^ A)) ∧
  (∃ (k : ℕ) (Q : ℝ) (lam : Fin k → ℝ) (mu : Fin k → ℂ) (ω : ℂ),
    0 < Q ∧ (∀ i, 0 < lam i) ∧ (∀ i, 0 ≤ (mu i).re) ∧ ‖ω‖ = 1 ∧
    let Φ : ℂ → ℂ := fun s => (Q : ℂ) ^ s * (∏ i, Gamma (lam i * s + mu i)) * F s
    ∀ s : ℂ, 0 < s.re → s.re < 1 → Φ s = ω * starRingEnd ℂ (Φ (1 - starRingEnd ℂ s))) ∧
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ε) ∧
  (∃ (b : ℕ → ℂ) (θ : ℝ), θ < 1 / 2 ∧ (∀ n, ¬ IsPrimePow n → b n = 0) ∧
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖b n‖ ≤ C * (n : ℝ) ^ θ) ∧
    ∀ s : ℂ, 1 < s.re → LSeriesSummable b s ∧ F s = exp (LSeries b s))

/-- Selberg's Riemann hypothesis for the Selberg class. -/
theorem main :
    ∀ (a : ℕ → ℂ) (F : ℂ → ℂ), InSelbergClass a F →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → F s = 0 → s.re = 1 / 2 := by
  sorry

end OMA.S_wp_generalized_riemann_hypothesis_for_selberg_class
