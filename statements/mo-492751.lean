import Mathlib

/-!
# Gaussian inverse covariance after optimal column selection

Source: Drew Brady, https://mathoverflow.net/questions/492751 (CC BY-SA 4.0).
Credit: @connoranderson. The deterministic upper bound uses the volume-sampling
principle of Michał Dereziński and Manfred K. Warmuth, https://arxiv.org/abs/1705.06908.
The Cauchy–Binet formalization adapts the public OAI.Problem336.CauchyBinet proof
in proofs/Erdos20.erdos_20.R1.H2.R1.H1.R1.H2.R1.H4.lean of Open Math Agents.

For n positive and N at least n, consider an n-by-N independent standard Gaussian
matrix. Select n columns to minimize the inverse sample-covariance quadratic form
in a fixed unit direction. Its expectation is finite exactly when N is at least
n+2. In this range it lies between n/(N-n-1) and n(N-n+1)/(N-n-1). The extended
nonnegative real formulation includes divergence at N=n and N=n+1. The value is
the same for every unit direction.
-/
namespace OMA.S_mo_492751
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n N : ℕ) := Matrix (Fin n) (Fin N) ℝ
noncomputable def normalLaw (d : ℕ) : Measure (Vec d) := Measure.pi (fun _ => gaussianReal 0 1)

noncomputable def gram {n N : ℕ} (A : Mat n N) (S : Finset (Fin N)) : Mat n n :=
  A * (Matrix.diagonal (fun j => if j∈S then (1:ℝ) else 0) * Aᵀ)

/-- The scaled inverse-covariance cost; singular subsets have infinite cost. -/
noncomputable def subsetCost {n N : ℕ} (A : Mat n N) (u : Vec n) (S : Finset (Fin N)) : ℝ≥0∞ :=
  if (gram A S).det = 0 then ⊤ else
    ENNReal.ofReal ((n:ℝ)*(u ⬝ᵥ ((gram A S)⁻¹ *ᵥ u)))

noncomputable def bestCost {n N : ℕ} (A : Mat n N) (u : Vec n) : ℝ≥0∞ :=
  ⨅ S : {S : Finset (Fin N) // S.card = n}, subsetCost A u S.val

abbrev E (N : ℕ) := EuclideanSpace ℝ (Fin N)
noncomputable def rowLaw (n N : ℕ) : Measure (Fin n → E N) := Measure.pi (fun _ => stdGaussian (E N))
instance rowLaw_prob (n N : ℕ) : IsProbabilityMeasure (rowLaw n N) := by unfold rowLaw; infer_instance
def raw {n N : ℕ} (rows : Fin n → E N) : Mat n N := Matrix.of (fun i j => rows i j)
noncomputable def expected {n : ℕ} (N : ℕ) (u : Vec n) : ℝ≥0∞ :=
  ∫⁻ rows : Fin n → E N, bestCost (raw rows) u ∂rowLaw n N

theorem main : ∀ (n N : ℕ), 0 < n → n ≤ N → ∀ (u : Vec n), (∑ i, (u i)^2) = 1 →
    (n : ℝ≥0∞) * ((N-n-1 : ℕ) : ℝ≥0∞)⁻¹ ≤ expected N u ∧
    expected N u ≤ (n : ℝ≥0∞) * (N-n+1 : ℕ) * ((N-n-1 : ℕ) : ℝ≥0∞)⁻¹ ∧
    (expected N u < ⊤ ↔ n+2 ≤ N) ∧
    ∀ v : Vec n, (∑ i, (v i)^2) = 1 → expected N u = expected N v := by
  sorry

end OMA.S_mo_492751
