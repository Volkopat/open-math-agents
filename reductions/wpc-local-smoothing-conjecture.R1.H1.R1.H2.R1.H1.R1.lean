import OMAReductions.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
open MeasureTheory OMA.S_wpc_local_smoothing_conjecture
open scoped ComplexConjugate ContDiff ENNReal RealInnerProductSpace
noncomputable section
namespace OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1_H1_R1
theorem angularFourier_conj {n : ℕ} (f : Space n → ℂ) (ξ : Space n) :
    angularFourier (fun x ↦ conj (f x)) ξ = conj (angularFourier f (-ξ)) := by
  unfold angularFourier
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [← Complex.exp_conj]

theorem angularInverse_conj {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    angularInverse (fun ξ ↦ conj (g ξ)) x = conj (angularInverse g (-x)) := by
  unfold angularInverse
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  rw [← integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp [← Complex.exp_conj]

theorem angularInverse_neg {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    angularInverse (fun ξ ↦ g (-ξ)) x = angularInverse g (-x) := by
  unfold angularInverse
  congr 1
  have h := integral_neg_eq_self (fun ξ : Space n ↦
    Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g (-ξ)) volume
  simpa only [neg_neg, inner_neg_right, inner_neg_left] using h.symm

theorem frequencyHalfWave_conj {n : ℕ} (φ f : Space n → ℂ) (h t : ℝ) (x : Space n) :
    let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : Space n → ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
    W (fun ξ => conj (φ (-ξ))) h t (fun y => conj (f y)) x =
      conj (W φ h (-t) f x) := by
  dsimp only
  let g : Space n → ℂ := fun ξ => Complex.exp (-Complex.I * ((-t) * ‖ξ‖ : ℝ)) *
    φ (h • ξ) * angularFourier f ξ
  have he : (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
      conj (φ (-(h • ξ))) * angularFourier (fun y => conj (f y)) ξ) =
      (fun ξ => conj (g (-ξ))) := by
    funext ξ
    rw [angularFourier_conj]
    simp [g, ← Complex.exp_conj, smul_neg]
  rw [he, angularInverse_conj,
    angularInverse_neg, neg_neg]


def H1 : Prop := (∀ (n : ℕ), 2 ≤ n → ∀ φ : Space n → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → 0 ∉ tsupport φ →
    let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : Space n → ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
    let q := ENNReal.ofReal (2*(n:ℝ)/(n-1))
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ, MemLp (fun z : Space n × ℝ => W φ h z.2 f z.1) q (observationMeasure n) ∧ eLpNorm (fun z : Space n × ℝ => W φ h z.2 f z.1) q (observationMeasure n) ≤ .ofReal (C*(1+Real.log (1/h))^(2*n+5)) * eLpNorm f q volume) →
  ∀ (n : ℕ), 2 ≤ n → ∀ p : ℝ, 2*(n:ℝ)/(n-1) ≤ p →
  let b : ContDiffBump (0 : Space n) := ⟨8,16,by norm_num,by norm_num⟩
  let l : Space n → ℂ := fun ξ => (b ξ : ℝ)
  let a : Space n → ℂ := fun ξ => l ((1/2:ℝ) • ξ) - l ξ
  let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : SchwartzMap (Space n) ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
  let P := ENNReal.ofReal p
  ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ, eLpNorm (fun z : Space n × ℝ => W a h z.2 f z.1) P (observationMeasure n) ≤ .ofReal (C*h^(-(((n:ℝ)-1)*(1/2-1/p)-1/p))*(1+Real.log (1/h))^(2*n+5)) * eLpNorm f P volume

def H2 : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ φ : Space n → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → 0 ∉ tsupport φ →
    let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : Space n → ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
    let q := ENNReal.ofReal (2*(n:ℝ)/(n-1))
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ, MemLp (fun z : Space n × ℝ => W φ h z.2 f z.1) q (observationMeasure n) ∧ eLpNorm (fun z : Space n × ℝ => W φ h z.2 f z.1) q (observationMeasure n) ≤ .ofReal (C*(1+Real.log (1/h))^(2*n+5)) * eLpNorm f q volume

theorem main : H1 → H2 → OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1.H1 := by
  intro I K n hn p hp
  let b : ContDiffBump (0 : Space n) := ⟨8,16,by norm_num,by norm_num⟩
  let a : Space n → ℂ := fun ξ => (b ((1/2:ℝ) • ξ) : ℝ) - (b ξ : ℝ)
  let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : Space n → ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
  have ha (ξ : Space n) : conj (a (-ξ)) = a ξ := by simp [a, smul_neg, ContDiffBump.neg]
  obtain ⟨C,hC,H⟩ := I K n hn p hp
  refine ⟨C,hC,fun h hh h1 f => ?_⟩
  let g := f.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have he (z : Space n × ℝ) : W a h z.2 g z.1 = conj (W a h (-z.2) f z.1) := by
    change W a h z.2 (fun y => conj (f y)) z.1 = _
    simpa only [W, ha] using frequencyHalfWave_conj a f h z.2 z.1
  have hnorm : eLpNorm (fun z : Space n × ℝ => W a h z.2 g z.1) (ENNReal.ofReal p) (observationMeasure n) = eLpNorm (fun z : Space n × ℝ => W a h (-z.2) f z.1) (ENNReal.ofReal p) (observationMeasure n) := by
    simp only [he]
    exact eLpNorm_conj _ _ _
  have hgn : eLpNorm g (ENNReal.ofReal p) volume = eLpNorm f _ volume := eLpNorm_conj (f : Space n → ℂ) _ _
  exact hnorm.symm.trans_le ((H h hh h1 g).trans_eq (congrArg (_ * ·) hgn))
end OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1_H1_R1
