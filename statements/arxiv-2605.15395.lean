import Mathlib

/-!
# arXiv:2605.15395 — Equivalence and Separation for Multivariate Matrix-Exponential and Phase-Type Distribution Classes

Author: Oscar Peralta.

We formalize the main results of the paper resolving the two open questions of Bladt and Nielsen (2010):
1. **Theorem 3.4 (`MVME_n = MME*_n`)**: For all `n ≥ 2`, every rational multivariate transform
   `P(s)/Q(s)` with `Q(0) ≠ 0` and `P(0) = Q(0)` admits a normalized Kulkarni-form algebraic
   representation `p₀ + α (-T + Δ(K s))⁻¹ t` with `T` Hurwitz-stable, `K ≥ 0`, `t = -T 1`,
   `p₀ = 1 - α 1`, `0 ≤ α 1 ≤ 1` (and conversely, every such Kulkarni representation defines
   a rational function analytic at the origin).
2. **Theorem 4.2 (`MPH*_n` factorization criterion)**: If a reduced rational transform `P(s)/Q(s)`
   (`P, Q` coprime, `Q ≠ 0`) admits an `MPH*_n` representation, then up to a nonzero scalar
   multiple of `Q`, its leading homogeneous part `Q_top` factors as a positive scalar multiple
   of a product of real linear forms with non-negative coefficients.
3. **Theorems 4.4, 4.5, and Corollary 4.6 (`MPH*_n ⊂neq MVPH_n` for all `n ≥ 3`)**: For every
   `n ≥ 3`, there exists a probability measure `μ` supported on `[0, ∞)^n` whose joint Laplace
   transform is rational and every positive projection `⟨a, X⟩` (`a ∈ [0, ∞)^n \ {0}`) has a
   univariate phase-type Laplace transform (`μ ∈ MVPH_n`), yet `μ` admits no finite-dimensional
   `MPH*_n` representation (constructed from a `2 × 2` Wishart trace law tensored with
   independent `Exp(1)` marginals).
-/

namespace OMA.S_arxiv_2605_15395

open Matrix MvPolynomial MeasureTheory

/-- A real `m × m` matrix `T` is Hurwitz-stable if every complex eigenvalue of `T` has
strictly negative real part. -/
def IsHurwitzStable {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ μ : ℂ, Polynomial.IsRoot (T.map Complex.ofReal).charpoly μ → μ.re < 0

/-- A real `m × m` matrix `T` is a transient Markov subgenerator if it is Hurwitz-stable,
has strictly negative diagonal entries, non-negative off-diagonal entries, and non-positive
row sums `T 1 ≤ 0`. -/
def IsTransientSubgenerator {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  IsHurwitzStable T ∧
  (∀ i : Fin m, T i i < 0) ∧
  (∀ i j : Fin m, i ≠ j → 0 ≤ T i j) ∧
  (∀ i : Fin m, ∑ j : Fin m, T i j ≤ 0)

/-- The Kulkarni diagonal resolvent evaluation
`p₀ + α (-T + diag(K s))⁻¹ t` for a triplet `(α, T, K)`, closing vector `t`, and atom `p₀`. -/
noncomputable def kulkarniEval {m n : ℕ} (p₀ : ℝ) (α : Fin m → ℝ)
    (T : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ)
    (s : Fin n → ℝ) : ℝ :=
  p₀ + dotProduct α ((-T + Matrix.diagonal (K.mulVec s))⁻¹.mulVec t)

/-- A function `L : ℝ → ℝ` is the Laplace transform of a univariate phase-type (`PH`) distribution
on `[0, ∞)` if it has a transient Markov representation `p₀ + α (u I - T)⁻¹ (-T 1)` for `u ≥ 0`. -/
def IsUnivariatePHTransform (L : ℝ → ℝ) : Prop :=
  ∃ (m : ℕ) (_ : 1 ≤ m) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ),
    IsTransientSubgenerator T ∧
    (∀ i, 0 ≤ α i) ∧
    (∑ i, α i ≤ 1) ∧
    ∀ u : ℝ, 0 ≤ u →
      IsUnit (u • (1 : Matrix (Fin m) (Fin m) ℝ) - T).det ∧
      L u = (1 - ∑ i, α i) +
        dotProduct α ((u • (1 : Matrix (Fin m) (Fin m) ℝ) - T)⁻¹.mulVec (-(T.mulVec 1)))

/-- A function `L : (Fin n → ℝ) → ℝ` admits an `MPH*_n` (Markovian Kulkarni reward)
representation on `[0, ∞)^n`. -/
def HasMPHRep {n : ℕ} (L : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (m : ℕ) (_ : 1 ≤ m) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin m) (Fin n) ℝ),
    IsTransientSubgenerator T ∧
    (∀ i, 0 ≤ α i) ∧
    (∑ i, α i ≤ 1) ∧
    (∀ i j, 0 ≤ K i j) ∧
    ∀ s : Fin n → ℝ, (∀ j, 0 ≤ s j) →
      IsUnit (-T + Matrix.diagonal (K.mulVec s)).det ∧
      L s = kulkarniEval (1 - ∑ i, α i) α T K (-(T.mulVec 1)) s

/-- Leading homogeneous part `F_top` of a multivariate polynomial `F`: the homogeneous component
of total degree `F.totalDegree`. -/
noncomputable def leadingHomog {n : ℕ} (F : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  F.homogeneousComponent F.totalDegree

/-- The Laplace transform `s ↦ ∫ x, exp (-⟨s, x⟩) ∂μ` of a measure `μ` on `Fin n → ℝ`. -/
noncomputable def laplaceTransform {n : ℕ} (μ : Measure (Fin n → ℝ)) (s : Fin n → ℝ) : ℝ :=
  ∫ x, Real.exp (-(∑ j : Fin n, s j * x j)) ∂μ

theorem main :
    -- Part 1: Equivalence `MVME_n = MME*_n` (Theorem 3.4 & Remark 2.4)
    (∀ (n : ℕ), 2 ≤ n →
      ∀ (P Q : MvPolynomial (Fin n) ℝ) (p₀ : ℝ),
        MvPolynomial.eval 0 Q ≠ 0 →
        MvPolynomial.eval 0 P = MvPolynomial.eval 0 Q →
        0 ≤ p₀ → p₀ ≤ 1 →
        ∃ (m : ℕ) (_ : 1 ≤ m) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
          (K : Matrix (Fin m) (Fin n) ℝ),
          IsHurwitzStable T ∧
          (∀ i j, 0 ≤ K i j) ∧
          p₀ = 1 - ∑ i, α i ∧
          0 ≤ ∑ i, α i ∧ ∑ i, α i ≤ 1 ∧
          ∃ U : Set (Fin n → ℝ), IsOpen U ∧ (0 : Fin n → ℝ) ∈ U ∧
            ∀ s ∈ U,
              MvPolynomial.eval s Q ≠ 0 ∧
              IsUnit (-T + Matrix.diagonal (K.mulVec s)).det ∧
              MvPolynomial.eval s P / MvPolynomial.eval s Q =
                kulkarniEval p₀ α T K (-(T.mulVec 1)) s) ∧
    (∀ (n m : ℕ) (p₀ : ℝ) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
      (K : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ),
      IsHurwitzStable T →
      ∃ P Q : MvPolynomial (Fin n) ℝ,
        MvPolynomial.eval 0 Q ≠ 0 ∧
        ∀ s : Fin n → ℝ, IsUnit (-T + Matrix.diagonal (K.mulVec s)).det →
          MvPolynomial.eval s Q ≠ 0 ∧
          kulkarniEval p₀ α T K t s = MvPolynomial.eval s P / MvPolynomial.eval s Q) ∧
    -- Part 2: `MPH*_n` factorization criterion (Theorem 4.2)
    (∀ (n : ℕ) (P Q : MvPolynomial (Fin n) ℝ),
      Q ≠ 0 →
      (∀ D : MvPolynomial (Fin n) ℝ, D ∣ P → D ∣ Q → IsUnit D) →
      (∃ (m : ℕ) (_ : 1 ≤ m) (α : Fin m → ℝ) (T : Matrix (Fin m) (Fin m) ℝ)
        (K : Matrix (Fin m) (Fin n) ℝ),
        IsTransientSubgenerator T ∧
        (∀ i, 0 ≤ α i) ∧
        (∑ i, α i ≤ 1) ∧
        (∀ i j, 0 ≤ K i j) ∧
        ∀ s : Fin n → ℝ, (∀ j, 0 ≤ s j) →
          MvPolynomial.eval s Q ≠ 0 ∧
          IsUnit (-T + Matrix.diagonal (K.mulVec s)).det ∧
          MvPolynomial.eval s P / MvPolynomial.eval s Q =
            kulkarniEval (1 - ∑ i, α i) α T K (-(T.mulVec 1)) s) →
      ∃ (c : ℝ) (hc : c ≠ 0) (c₀ : ℝ) (_ : 0 < c₀) (ν : ℕ) (lam : Fin ν → Fin n → ℝ),
        (∀ i j, 0 ≤ lam i j) ∧
        MvPolynomial.C c * leadingHomog Q =
          MvPolynomial.C c₀ * ∏ i : Fin ν, ∑ j : Fin n, MvPolynomial.C (lam i j) * MvPolynomial.X j) ∧
    -- Part 3: Strict separation `MPH*_n ⊂neq MVPH_n` for all `n ≥ 3` (Theorems 4.4, 4.5, Corollary 4.6)
    (∀ (n : ℕ), 3 ≤ n →
      ∃ μ : Measure (Fin n → ℝ),
        IsProbabilityMeasure μ ∧
        (∀ᵐ x ∂μ, ∀ j : Fin n, 0 ≤ x j) ∧
        (∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) → a ≠ 0 →
          IsUnivariatePHTransform (fun u => laplaceTransform μ (u • a))) ∧
        ¬ HasMPHRep (laplaceTransform μ)) := by
  sorry

end OMA.S_arxiv_2605_15395
