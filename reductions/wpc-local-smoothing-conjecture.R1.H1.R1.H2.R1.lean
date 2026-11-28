import OMAReductions.R_wpc_local_smoothing_conjecture_R1_H1_R1
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
open MeasureTheory OMA.S_wpc_local_smoothing_conjecture
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1
def H1 : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ p : ℝ, 2*(n:ℝ)/(n-1) ≤ p →
  let b : ContDiffBump (0 : Space n) := ⟨8,16,by norm_num,by norm_num⟩
  let l : Space n → ℂ := fun ξ => (b ξ : ℝ)
  let a : Space n → ℂ := fun ξ => l ((1/2:ℝ) • ξ) - l ξ
  let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : SchwartzMap (Space n) ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
  let P := ENNReal.ofReal p
  ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ, eLpNorm (fun z : Space n × ℝ => W a h (-z.2) f z.1) P (observationMeasure n) ≤ .ofReal (C*h^(-(((n:ℝ)-1)*(1/2-1/p)-1/p))*(1+Real.log (1/h))^(2*n+5)) * eLpNorm f P volume

def H2 : Prop := ∀ (n : ℕ) (α : ℝ) (P : ℝ≥0∞), 1 ≤ P → P ≠ ⊤ →
  let b : ContDiffBump (0 : Space n) := ⟨8,16,by norm_num,by norm_num⟩
  let l : Space n → ℂ := fun ξ => (b ξ : ℝ)
  let a : Space n → ℂ := fun ξ => l ((1/2:ℝ) • ξ) - l ξ
  let W := fun (φ : Space n → ℂ) (h t : ℝ) (f : SchwartzMap (Space n) ℂ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ)
  let d := fun j : ℕ => ((2:ℝ)⁻¹ ^ j)
  ∃ B : ℝ, 0 ≤ B ∧ ∀ (j : ℕ) (f : SchwartzMap (Space n) ℂ), ∃ g : SchwartzMap (Space n) ℂ, (∀ t x, W a (d j) t g x = W a (d j) t f x) ∧ eLpNorm g P volume ≤ .ofReal (B * d j ^ α) * eLpNorm (besselPotential α f) P volume

def H3 : Prop := ∀ (A : ℕ) (ε : ℝ), 0 < ε →
  let d := fun j : ℕ => ((2:ℝ)⁻¹ ^ j)
  Summable (fun j => d j ^ ε * (1+Real.log (1/d j))^A)

theorem main : H1 → H2 → H3 → OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1.H2 := by
  intro freq inv series n hn p α hp hα
  let s := (((n:ℝ)-1)*(1/2-1/p)-1/p)
  let d := fun j : ℕ => ((2:ℝ)⁻¹ ^ j)
  let w := fun j => d j ^ (α-s) * (1+Real.log (1/d j))^(2*n+5)
  have hd (j) : 0 < d j := by dsimp [d]; positivity
  have hd1 (j) : d j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hlog (j) : 0 ≤ 1+Real.log (1/d j) := by
    have h := Real.log_nonneg ((le_div_iff₀ (hd j)).mpr (by simpa using hd1 j))
    linarith
  have hw (j) : 0 ≤ w j := mul_nonneg (Real.rpow_nonneg (hd j).le _) (pow_nonneg (hlog j) _)
  have hsum : Summable w := series _ _ (sub_pos.mpr hα)
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n:ℝ)-1 := by linarith
  have hc := (div_le_iff₀ hden).mp hp
  have hp1 : 1 ≤ p := by by_contra! h; nlinarith [mul_lt_mul_of_pos_right h hden]
  have hP : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp1
  obtain ⟨C,hC,H⟩ := freq n hn p hp
  obtain ⟨B,hB,I⟩ := inv n α _ hP ENNReal.ofReal_ne_top
  refine ⟨(C*B)*(∑' j, w j),mul_nonneg (mul_nonneg hC hB) (tsum_nonneg hw),fun f => ?_⟩
  rw [ENNReal.ofReal_mul (mul_nonneg hC hB), ENNReal.ofReal_tsum_of_nonneg hw hsum, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro j
  obtain ⟨g,heq,hg⟩ := I j f
  have h := H (d j) (hd j) (hd1 j) g
  have eqNorm := congrArg (fun F : Space n × ℝ → ℂ => eLpNorm F (ENNReal.ofReal p) (observationMeasure n)) (funext (fun z : Space n × ℝ => heq (-z.2) z.1))
  apply (eqNorm.symm.trans_le h).trans ((mul_le_mul' le_rfl hg).trans_eq ?_)
  have hnC : 0 ≤ C * d j ^ (-s) * (1+Real.log (1/d j))^(2*n+5) := mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (hd j).le _)) (pow_nonneg (hlog j) _)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hnC, ← ENNReal.ofReal_mul (mul_nonneg hC hB)]
  congr 2
  change C*d j^(-s)*(1+Real.log (1/d j))^(2*n+5)*(B*d j^α) = C*B*(d j^(α-s)*(1+Real.log (1/d j))^(2*n+5))
  rw [sub_eq_add_neg, Real.rpow_add (hd j)]
  ring
end OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1
