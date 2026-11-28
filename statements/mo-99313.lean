import Mathlib

/-!
# Bounding the probability that a random variable is maximal

Source: https://mathoverflow.net/questions/99313
Problem by MLS (MathOverflow; CC BY-SA 3.0).

For a finite family with finite second moments we prove the proposed lower bound
(2) on the winning coordinate's expected mean. With measurable tie-breaking the
factor improves to the square root of one minus the reciprocal of the family
size. The same bound holds under arbitrary dependence. A separate inequality
bounds each winning probability by comparing against a weighted combination
of competitors, with an explicit variance formula under independence. Uniform
finite examples show sharpness for the class allowing dependence.
-/

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology ProbabilityTheory
namespace OMA.S_mo_99313

noncomputable def winProb {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (I : Ω → Fin n) (i : Fin n) := μ.real {ω | I ω = i}

noncomputable def mean {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → ℝ) (i : Fin n) := ∫ ω, X i ω ∂μ

def Wins {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → ℝ) (I : Ω → Fin n) : Prop :=
  Measurable I ∧ ∀ᵐ ω ∂μ, ∀ j, X j ω ≤ X (I ω) ω

def contrast {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (w : Fin n → ℝ) (i : Fin n) (ω : Ω) :=
  ∑ j, (w j - (if j=i then 1 else 0)) * X j ω

/-- Moments on a uniform finite sample for the sharpness statement. -/
noncomputable def uniformMean {n : ℕ} (f : Fin n → ℝ) := (∑ s, f s) / n
noncomputable def uniformVar {n : ℕ} (f : Fin n → ℝ) :=
  uniformMean (fun s => (f s-uniformMean f)^2)

noncomputable def peakProb {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → ℝ) (i : Fin n) := μ.real {ω | ∀ j, X j ω ≤ X i ω}

theorem main :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n : ℕ) (hn : 0<n) (X : Fin n → Ω → ℝ) (hX : ∀i, MemLp (X i) 2 μ),
      (∀ (_ : ∀i, Measurable (X i)) (_ : ∀ᵐ ω ∂μ, ∃! i, ∀j, X j ω ≤ X i ω) (j : Fin n),
        mean μ X j - Real.sqrt (∑ i, variance (X i) μ) ≤ ∑ i, mean μ X i * peakProb μ X i) ∧
      ∀ I : Ω → Fin n, Wins μ X I →
        (∀ j, mean μ X j - ∑ i, mean μ X i * winProb μ I i ≤
          Real.sqrt (1-1/(n:ℝ)) * Real.sqrt (∑ i, variance (X i) μ)) ∧
        ∀ (i : Fin n) (w : Fin n → ℝ), (∀ j, 0≤w j) → ∑ j, w j=1 →
          0 ≤ (∑ j, w j*mean μ X j) - mean μ X i →
          winProb μ I i * ((∑ j, w j*mean μ X j) - mean μ X i)^2 ≤
            (1-winProb μ I i)*variance (contrast X w i) μ ∧
          (iIndepFun X μ → variance (contrast X w i) μ =
            ∑ j, (w j-(if j=i then 1 else 0))^2 * variance (X j) μ)) ∧
    ∀ (n : ℕ), 2≤n → ∀ (a : ℝ), 0≤a → a≤1 →
      ∃ (Y : Fin n → Fin n → ℝ) (j : Fin n),
        (∀ s k, Y k s ≤ Y s s) ∧
        (a<1 → ∀ s k, k≠s → Y k s < Y s s) ∧
        (0 < ∑ i, uniformVar (Y i)) ∧
        uniformMean (Y j) - uniformMean (fun i => uniformMean (Y i)) =
          a * Real.sqrt (1-1/(n:ℝ)) * Real.sqrt (∑ i, uniformVar (Y i)) := by
  sorry

end OMA.S_mo_99313
