import Mathlib

/-!
# Convergence of Laplace transforms at rate 1/n and pointwise convergence

Source: https://mathoverflow.net/questions/353531
Asked by MathOverflow user Wenguang Zhao (Point wise convergence of Laplace transform and
convergence of functions).

Let `f_n, f ∈ C_b(ℝ_+)` be such that for every `λ > 0`
`|∫_0^∞ e^{-λt} f_n(t) dt - ∫_0^∞ e^{-λt} f(t) dt| ≤ C_λ n^{-1}` with a constant `C_λ > 0`.
The question asks whether then `f_n(t) → f(t)` for every `t > 0`.

Translation choices.
* Functions are `ℝ → ℝ`; membership in `C_b(ℝ_+)` is continuity on `[0, ∞)` together with a
  uniform bound there (`IsCb`).
* The Laplace transform is `laplace g λ = ∫ t in (0, ∞), exp(-(λ t)) * g t`.
* The hypothesis is required for all `n ≥ 1`, and `main` is the affirmative answer to the
  first question (the question about the order of convergence is not formalized).
-/

namespace OMA.S_mo_353531

/-- `g` is a bounded continuous function on `ℝ_+ = [0, ∞)`. -/
def IsCb (g : ℝ → ℝ) : Prop :=
  ContinuousOn g (Set.Ici 0) ∧ ∃ M : ℝ, ∀ t, 0 ≤ t → |g t| ≤ M

/-- The Laplace transform `∫_0^∞ e^{-λt} g(t) dt`. -/
noncomputable def laplace (g : ℝ → ℝ) (lam : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(lam * t)) * g t

theorem main :
    ∀ (fs : ℕ → ℝ → ℝ) (f : ℝ → ℝ), (∀ n, IsCb (fs n)) → IsCb f →
      (∀ lam : ℝ, 0 < lam → ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, 1 ≤ n → |laplace (fs n) lam - laplace f lam| ≤ C / n) →
      ∀ t : ℝ, 0 < t → Filter.Tendsto (fun n => fs n t) Filter.atTop (nhds (f t)) := by
  sorry

end OMA.S_mo_353531
