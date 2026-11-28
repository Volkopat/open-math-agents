import OMAStatements.S_arxiv_2606_14687

-- Credit: @ryansolves
namespace OMA.R_arxiv_2606_14687_R1
open OMA.S_arxiv_2606_14687 Filter MeasureTheory Matrix
open scoped BigOperators Topology
noncomputable section

private theorem transverseCov {d r : ℕ} (R : Matrix (Fin r) (Fin d) ℝ)
    (v : Vec d) (hv : R.mulVec v = 0) (S : CMat d) (θ : ℝ) :
    R * predictedCov θ v S * R.transpose =
    R * (show Mat d from fun i j => (S i j).re) * R.transpose := by
  change R * (_ - _ • vecMulVec v v) * _ = _
  rw [Matrix.mul_sub, Matrix.mul_smul, mul_vecMulVec, hv]
  simp

private theorem quadratic_limit {r : ℕ} (B : ℕ → Mat r) (Γ : Mat r) (t : Vec r)
    (lim : ∀ i j, Tendsto (fun n : ℕ => (n+1 : ℝ) * B n i j) atTop (𝓝 (Γ i j))) :
    Tendsto (fun n : ℕ => (n+1 : ℝ) * realDot t ((B n).mulVec t)) atTop
      (𝓝 (realDot t (Γ.mulVec t))) := by
  have h : Tendsto (fun n : ℕ => ∑ i, ∑ j, t i * (((n+1 : ℝ) * B n i j) * t j)) atTop
      (𝓝 (∑ i, ∑ j, t i * (Γ i j * t j))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      tendsto_const_nhds.mul ((lim i j).mul tendsto_const_nhds)
  convert h using 1 <;>
    simp only [realDot, mulVec, dotProduct, Finset.mul_sum, mul_left_comm, mul_assoc, mul_comm]

/-- Scalar Gaussianity from convergence of the actual second moment. -/
def H1 : Prop :=
    ∀ (θ : ℝ), 1 < θ →
    ∀ (k : ℕ → ℕ) (A : (n : ℕ) → Fin (k n) → Mat (n + 1))
      (v : (n : ℕ) → Vec (n + 1))
      (w : (n : ℕ) → Vec (k n) → Vec (n + 1)),
    (∀ n j, (A n j).IsSymm) →
    (∀ n, ∑ j, A n j * A n j = 1) →
    (∃ b : ℕ → ℝ, (∀ n, boundsCovariance (A n) (b n)) ∧
      Tendsto (fun n : ℕ => b n * (Real.log (n + 1 : ℝ)) ^ (3 / 2 : ℝ)) atTop (𝓝 0)) →
    (∀ n, realDot (v n) (v n) = 1) →
    (∀ n, AEMeasurable (w n) (standardInputs (k n))) →
    (∀ n, ∀ᵐ g ∂standardInputs (k n),
      isTopUnitVector (θ • projector (v n) + ∑ j, (g j) • A n j) (w n g) ∧
      0 < realDot (w n g) (v n)) →
    (∀ n, ∃! S : CMat (n + 1), dualOptimizer (θ • projector (v n)) (A n) S) →
    ∀ (q : (n : ℕ) → Vec (n+1)),
    (∀ n, realDot (q n) (v n) = 0) →
    (∃ K : ℝ, ∀ n x, realDot (q n) x ^ 2 ≤ K * realDot x x) →
    ∀ γ : ℝ, Tendsto (fun n : ℕ => ∫ g,
      (Real.sqrt (n+1 : ℝ) * realDot (q n) (w n g)) ^ 2 ∂standardInputs (k n)) atTop (𝓝 γ) →
    Tendsto (fun n : ℕ => ∫ g, Complex.exp (Complex.I *
      ((Real.sqrt (n+1 : ℝ) * realDot (q n) (w n g)) : ℂ)) ∂standardInputs (k n))
      atTop (𝓝 (Complex.exp ((-γ/2 : ℝ) : ℂ)))

/-- Identification of the scalar second moment with either SDP prediction in transverse directions. -/
def H2 : Prop :=
    ∀ (θ : ℝ), 1 < θ →
    ∀ (k : ℕ → ℕ) (A : (n : ℕ) → Fin (k n) → Mat (n + 1))
      (v : (n : ℕ) → Vec (n + 1))
      (w : (n : ℕ) → Vec (k n) → Vec (n + 1)),
    (∀ n j, (A n j).IsSymm) →
    (∀ n, ∑ j, A n j * A n j = 1) →
    (∃ b : ℕ → ℝ, (∀ n, boundsCovariance (A n) (b n)) ∧
      Tendsto (fun n : ℕ => b n * (Real.log (n + 1 : ℝ)) ^ (3 / 2 : ℝ)) atTop (𝓝 0)) →
    (∀ n, realDot (v n) (v n) = 1) →
    (∀ n, AEMeasurable (w n) (standardInputs (k n))) →
    (∀ n, ∀ᵐ g ∂standardInputs (k n),
      isTopUnitVector (θ • projector (v n) + ∑ j, (g j) • A n j) (w n g) ∧
      0 < realDot (w n g) (v n)) →
    (∀ n, ∃! S : CMat (n + 1), dualOptimizer (θ • projector (v n)) (A n) S) →
    ∀ (q : (n : ℕ) → Vec (n+1)),
    (∀ n, realDot (q n) (v n) = 0) →
    (∃ K : ℝ, ∀ n x, realDot (q n) x ^ 2 ≤ K * realDot x x) →
    ∀ (S : (n : ℕ) → CMat (n + 1)),
    ((∀ n, dualOptimizer (θ • projector (v n)) (A n) (S n)) ∨
      (∀ n, certificateHypotheses (A n) ∧ estimatedCertificate θ (v n) (A n) (S n))) →
    ∀ γ : ℝ, Tendsto (fun n : ℕ => (n+1 : ℝ) * realDot (q n)
      ((show Mat (n+1) from fun i j => (S n i j).re).mulVec (q n))) atTop (𝓝 γ) →
    Tendsto (fun n : ℕ => ∫ g,
      (Real.sqrt (n+1 : ℝ) * realDot (q n) (w n g)) ^ 2 ∂standardInputs (k n)) atTop (𝓝 γ)

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2606_14687.main := by
  intro gaussian variance θ hθ k A v w sym iso small unit meas leading unique S admissible
    r _ R Γ _ transverse bound limit t
  let q := fun n : ℕ => vecMul t (R n)
  have proj (n : ℕ) (x : Vec (n+1)) :
      realDot t ((R n).mulVec x) = realDot (q n) x := dotProduct_mulVec .. 
  have orthogonal : ∀ n, realDot (q n) (v n) = 0 := fun n => by
      change realDot (q n) (v n) = 0
      rw [← proj, transverse]
      simp [realDot]
  have bounded : ∃ K : ℝ, ∀ n x, realDot (q n) x ^ 2 ≤ K * realDot x x := by
      obtain ⟨C,hC⟩ := bound
      refine ⟨realDot t t * C^2, fun n x => ?_⟩
      change realDot (q n) x ^ 2 ≤ _
      rw [← proj]
      have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ t ((R n).mulVec x)
      have nonneg : 0 ≤ realDot t t := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
      calc
        _ ≤ realDot t t * realDot ((R n).mulVec x) ((R n).mulVec x) := by
          simpa [realDot, pow_two] using cs
        _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hC n x) nonneg
  let B := fun n : ℕ => R n * predictedCov θ (v n) (S n) * (R n).transpose
  have cov (n : ℕ) : realDot t ((B n).mulVec t) = realDot (q n)
      ((show Mat (n+1) from fun i j => (S n i j).re).mulVec (q n)) := by
    dsimp only [B]
    rw [transverseCov _ _ (transverse n), ← mulVec_mulVec, ← mulVec_mulVec,
      mulVec_transpose, proj]
  have limit' := quadratic_limit B Γ t limit
  simp_rw [cov] at limit'
  have answer := gaussian θ hθ k A v w sym iso small unit meas leading unique q orthogonal bounded _
    (variance θ hθ k A v w sym iso small unit meas leading unique q orthogonal bounded S admissible _ limit')
  simpa only [Complex.ofReal_mul, Matrix.mulVec_sub, Matrix.mulVec_smul, transverse,
    smul_zero, sub_zero, proj] using answer

end
end OMA.R_arxiv_2606_14687_R1
