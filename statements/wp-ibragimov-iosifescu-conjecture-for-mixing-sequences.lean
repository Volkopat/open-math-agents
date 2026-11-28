import Mathlib

/-!
# Ibragimov–Iosifescu conjecture for φ-mixing sequences

Source: https://en.wikipedia.org/wiki/Ibragimov–Iosifescu_conjecture_for_φ-mixing_sequences
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Ibragimov): let `(X_n)` be a strictly stationary `φ`-mixing sequence with
`E X₀² < ∞` and `Var(S_n) → ∞`, where `S_n = X_1 + ⋯ + X_n`. Then `S_n` is asymptotically
normally distributed.

Conventions:
* We state Ibragimov's central limit theorem form (the first of the two conjectures collected
  under this name): `(S_n - E S_n) / √Var(S_n)` converges in distribution to `N(0,1)`, written via
  pointwise convergence of distribution functions (the limit's distribution function is
  continuous, so this is equivalent to weak convergence).
* The sequence is indexed by `ℕ` and `S_n = X_0 + ⋯ + X_{n-1}`; by stationarity this is the same
  as the source's indexing.
* Strict stationarity: every finite block `(X_k, …, X_{k+n})` has the law of `(X_0, …, X_n)`.
* `φ`-mixing: `φ(n) = sup |P(B | A) - P(B)| → 0`, the supremum over `m`, `A ∈ σ(X_j : j ≤ m)`
  with `P(A) > 0` and `B ∈ σ(X_j : j ≥ m + n)`; equivalently `|P(A ∩ B) - P(A)P(B)| ≤ φ(n) P(A)`
  for all such `A, B` (this form also covers `P(A) = 0`).
-/

namespace OMA.S_wp_ibragimov_iosifescu_conjecture_for_mixing_sequences

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type} [MeasurableSpace Ω]

/-- `σ(X_j : j ≤ m)`. -/
def pastSigma (X : ℕ → Ω → ℝ) (m : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ Finset.range (m + 1), MeasurableSpace.comap (X j) inferInstance

/-- `σ(X_j : j ≥ m)`. -/
def futureSigma (X : ℕ → Ω → ℝ) (m : ℕ) : MeasurableSpace Ω :=
  ⨆ (j : ℕ) (_ : m ≤ j), MeasurableSpace.comap (X j) inferInstance

/-- Strict stationarity. -/
def StrictlyStationary (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ k n : ℕ, P.map (fun ω (i : Fin (n + 1)) => X (k + i) ω) = P.map (fun ω (i : Fin (n + 1)) => X i ω)

/-- `φ`-mixing. -/
def PhiMixing (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∃ φ : ℕ → ℝ, Tendsto φ atTop (nhds 0) ∧
    ∀ n m : ℕ, ∀ A B : Set Ω, MeasurableSet[pastSigma X m] A →
      MeasurableSet[futureSigma X (m + n)] B →
        |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| ≤ φ n * (P A).toReal

/-- The partial sum `S_n`. -/
def S (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := fun ω => ∑ j ∈ Finset.range n, X j ω

theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ),
      (∀ j, Measurable (X j)) → StrictlyStationary P X → PhiMixing P X → MemLp (X 0) 2 P →
      Tendsto (fun n => variance (S X n) P) atTop atTop →
        ∀ x : ℝ, Tendsto (fun n =>
          (P {ω | (S X n ω - P[S X n]) / Real.sqrt (variance (S X n) P) ≤ x}).toReal) atTop
          (nhds (cdf (gaussianReal 0 1) x)) := by
  sorry

end OMA.S_wp_ibragimov_iosifescu_conjecture_for_mixing_sequences
