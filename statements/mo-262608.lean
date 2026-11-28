import Mathlib

/-!
# First and second moment bounds for expected matrix square roots

For a random positive semidefinite Hermitian matrix U write mᵢ for the ith
diagonal entry of E[U] and sᵢ for the ith diagonal entry of E[U²]. For
square-integrable entries, the trace of (E[√U])² lies between Σ mᵢ³/sᵢ and
Σ mᵢ. The matrices may have arbitrary dependence and need not commute.
The trace and the diagonal moments are real. A zero second moment contributes
zero to the lower bound under the usual Lean convention for division.

Fix any positive means and second moments sᵢ ≥ mᵢ². Even among finite laws of
strictly positive diagonal matrices, these two endpoints are the infimum and
supremum and every value strictly between them occurs. If singular matrices
are admitted the lower bound is attained. The finite laws are realized by
step functions of a single uniform point of (0,1].

Source: Cain, https://mathoverflow.net/questions/262608 (CC BY-SA 3.0).
The scalar supporting quadratic is adapted from Ori Gurel-Gurevich's
https://mathoverflow.net/a/121424 (CC BY-SA 3.0). The matrix proof uses
positive semidefinite congruence and optimizes its scale separately in each
coordinate. Explicit two-point marginals establish sharpness.
Credit: @connoranderson (agent: Codex).
-/
namespace OMA.S_mo_262608
open MeasureTheory Matrix
open scoped MatrixOrder ComplexOrder
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
noncomputable def first {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) (U : Ω → Mat n)
    (i : Fin n) : ℝ := ∫ ω, (U ω i i).re ∂μ
noncomputable def second {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) (U : Ω → Mat n)
    (i : Fin n) : ℝ := ∫ ω, ((U ω * U ω) i i).re ∂μ
noncomputable def meanRoot {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) (U : Ω → Mat n) : Mat n :=
  Matrix.of (fun i j => ∫ ω, (CFC.sqrt (U ω)) i j ∂μ)
noncomputable def quantity {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω) (U : Ω → Mat n) : ℝ :=
  ((meanRoot μ U * meanRoot μ U).trace).re
noncomputable def unitLaw : Measure ℝ := volume.restrict (Set.Ioc 0 1)
def fits {n : ℕ} (m s : Fin n → ℝ) (U : ℝ → Mat n) : Prop :=
  (∀ i j, MemLp (fun x => U x i j) 2 unitLaw) ∧ first unitLaw U = m ∧ second unitLaw U = s
def finiteDiagonal {n : ℕ} (U : ℝ → Mat n) : Prop :=
  (Set.range U).Finite ∧ ∀ x i j, i ≠ j → U x i j = 0
def diagonalValues {n : ℕ} (m s : Fin n → ℝ) : Set ℝ :=
  {q | ∃ U : ℝ → Mat n, (∀ x, (U x).PosDef) ∧ finiteDiagonal U ∧ fits m s U ∧ quantity unitLaw U = q}
end OMA.S_mo_262608
namespace OMA.S_mo_262608
open MeasureTheory
open scoped MatrixOrder ComplexOrder
theorem main :
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n : ℕ) (U : Ω → Mat n), (∀ᵐ ω ∂μ, (U ω).PosSemidef) →
      (∀ i j, MemLp (fun ω => U ω i j) 2 μ) →
      (∑ i, (first μ U i)^3 / second μ U i) ≤ quantity μ U ∧ quantity μ U ≤ ∑ i, first μ U i) ∧
    (∀ (n : ℕ) (m s : Fin n → ℝ), (∀ i, 0 < m i) → (∀ i, (m i)^2 ≤ s i) →
      (∃ U : ℝ → Mat n, (∀ x, (U x).PosSemidef) ∧ finiteDiagonal U ∧ fits m s U ∧
        quantity unitLaw U = ∑ i, (m i)^3/s i) ∧
      IsGLB (diagonalValues m s) (∑ i,(m i)^3/s i) ∧ IsLUB (diagonalValues m s) (∑ i,m i) ∧
      Set.Ioo (∑ i,(m i)^3/s i) (∑ i,m i) ⊆ diagonalValues m s) := by
  sorry
end OMA.S_mo_262608
