import OMAReductions.R_wpc_local_smoothing_conjecture_R1
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
open MeasureTheory OMA.S_wpc_local_smoothing_conjecture
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1
def H1 : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ (p α : ℝ), 2*(n:ℝ)/(n-1) ≤ p → ((n:ℝ)-1)*(1/2-1/p)-1/p < α →
  let b : ContDiffBump (0 : Space n) := ⟨8,16,by norm_num,by norm_num⟩
  let l : Space n → ℂ := fun ξ => (b ξ : ℝ)
  let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : SchwartzMap (Space n) ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
  let P := ENNReal.ofReal p
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap (Space n) ℂ, eLpNorm (besselPotential α f) P volume < ⊤ ∧ eLpNorm (fun z : Space n × ℝ => W l 1 (-z.2) f z.1) P (observationMeasure n) ≤ .ofReal C * eLpNorm (besselPotential α f) P volume

def H2 : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ (p α : ℝ), 2*(n:ℝ)/(n-1) ≤ p → ((n:ℝ)-1)*(1/2-1/p)-1/p < α →
  let b : ContDiffBump (0 : Space n) := ⟨8,16,by norm_num,by norm_num⟩
  let l : Space n → ℂ := fun ξ => (b ξ : ℝ)
  let a : Space n → ℂ := fun ξ => l ((1/2:ℝ) • ξ) - l ξ
  let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : SchwartzMap (Space n) ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
  let P := ENNReal.ofReal p
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap (Space n) ℂ, (∑' j : ℕ, eLpNorm (fun z : Space n × ℝ => W a ((2:ℝ)⁻¹ ^ j) (-z.2) f z.1) P (observationMeasure n)) ≤ .ofReal C * eLpNorm (besselPotential α f) P volume

def H3 : Prop := ∀ (n : ℕ) (P : ℝ≥0∞), 1 ≤ P →
  let b : ContDiffBump (0 : Space n) := ⟨8,16,by norm_num,by norm_num⟩
  let l : Space n → ℂ := fun ξ => (b ξ : ℝ)
  let a : Space n → ℂ := fun ξ => l ((1/2:ℝ) • ξ) - l ξ
  let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : SchwartzMap (Space n) ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
  ∀ f : SchwartzMap (Space n) ℂ, eLpNorm (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1) P (observationMeasure n) ≤ eLpNorm (fun z : Space n × ℝ => W l 1 (-z.2) f z.1) P (observationMeasure n) + ∑' j : ℕ, eLpNorm (fun z : Space n × ℝ => W a ((2:ℝ)⁻¹ ^ j) (-z.2) f z.1) P (observationMeasure n)

theorem main : H1 → H2 → H3 → OMA.R_wpc_local_smoothing_conjecture_R1.H1 := by
  intro hl ha ht n hn p α hp hα
  obtain ⟨L,hL,low⟩ := hl n hn p α hp hα
  obtain ⟨C,hC,ann⟩ := ha n hn p α hp hα
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-1 := by linarith
  have hc := (div_le_iff₀ hd).mp hp
  have hp1 : 1 ≤ p := by by_contra! h; nlinarith [mul_lt_mul_of_pos_right h hd]
  have hP : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp1
  refine ⟨L+C+1,by linarith,fun f => ⟨(low f).1,?_⟩⟩
  apply (ht n _ hP f).trans
  apply (add_le_add (low f).2 (ann f)).trans
  rw [← add_mul, ← ENNReal.ofReal_add hL hC]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
end OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1
