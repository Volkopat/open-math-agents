import OMAReductions.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1_H1_R1
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0),
   WavePackets/{Periodic,Euclidean,Logarithmic,AllScales}. -/
open MeasureTheory OMA.S_wpc_local_smoothing_conjecture
open scoped ContDiff ENNReal
noncomputable section
namespace OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1_H1_R1_H2_R1
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def H1 : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ φ : Space n → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → 0 ∉ tsupport φ →
  let p := ENNReal.ofReal (2*(n:ℝ)/(n-1))
  let freq := fun (k : Fin n → ℤ) => (2 * Real.pi / 100) • (WithLp.toLp 2 (fun i => (k i : ℝ)) : Space n)
  let periodicW := fun (h t : ℝ) (g : UnitAddTorus (Fin n) → ℂ) (x : UnitAddTorus (Fin n)) => ∑' k : Fin n → ℤ, Complex.exp (-Complex.I * ((t * ‖freq k‖ : ℝ) : ℂ)) * φ (h • freq k) * UnitAddTorus.mFourierCoeff g k * UnitAddTorus.mFourier k x
  let torusBound := fun (h : ℝ) (A : ℝ≥0∞) => ∀ g : UnitAddTorus (Fin n) → ℂ, Measurable g → MemLp g p volume →
    eLpNorm (fun z : ℝ × UnitAddTorus (Fin n) => periodicW h z.1 g z.2) p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤ A * eLpNorm g p volume
  let euclideanW := fun (h : ℝ) (f : SchwartzMap (Space n) ℂ) (z : Space n × ℝ) => angularInverse (fun ξ => Complex.exp (-Complex.I * (z.2 * ‖ξ‖ : ℝ)) * φ (h • ξ) * angularFourier f ξ) z.1
  ∃ K D : ℝ, 0 ≤ K ∧ 0 ≤ D ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ A : ℝ, 0 ≤ A → torusBound h (.ofReal A) →
    ∀ f : SchwartzMap (Space n) ℂ, MemLp (euclideanW h f) p (observationMeasure n) ∧
      eLpNorm (euclideanW h f) p (observationMeasure n) ≤ .ofReal (K*A+D) * eLpNorm f p volume

def H2 : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ φ : Space n → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → 0 ∉ tsupport φ →
  let p := ENNReal.ofReal (2*(n:ℝ)/(n-1))
  let freq := fun (k : Fin n → ℤ) => (2 * Real.pi / 100) • (WithLp.toLp 2 (fun i => (k i : ℝ)) : Space n)
  let periodicW := fun (h t : ℝ) (g : UnitAddTorus (Fin n) → ℂ) (x : UnitAddTorus (Fin n)) => ∑' k : Fin n → ℤ, Complex.exp (-Complex.I * ((t * ‖freq k‖ : ℝ) : ℂ)) * φ (h • freq k) * UnitAddTorus.mFourierCoeff g k * UnitAddTorus.mFourier k x
  let torusBound := fun (h : ℝ) (A : ℝ≥0∞) => ∀ g : UnitAddTorus (Fin n) → ℂ, Measurable g → MemLp g p volume →
    eLpNorm (fun z : ℝ × UnitAddTorus (Fin n) => periodicW h z.1 g z.2) p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤ A * eLpNorm g p volume
  ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → torusBound h (.ofReal (C*(1+Real.log (1/h))^(2*n+5)))

theorem main : H1 → H2 → OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1_H1_R1.H2 := by
  intro T P n hn φ hd hc hz
  obtain ⟨K,D,hK,hD,tr⟩ := T n hn φ hd hc hz
  obtain ⟨C,hC,per⟩ := P n hn φ hd hc hz
  refine ⟨K*C+D+1, by positivity, ?_⟩
  intro h hh h1 f
  let L := (1+Real.log (1/h))^(2*n+5)
  have hlog := Real.log_nonneg ((le_div_iff₀ hh).mpr (by simpa using h1) : 1 ≤ 1/h)
  have hL : 1 ≤ L := one_le_pow₀ (by linarith)
  obtain ⟨hm,hb⟩ := tr h hh h1 (C*L) (mul_nonneg hC.le (by linarith)) (per h hh h1) f
  refine ⟨hm, hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)⟩
  change K*(C*L)+D ≤ (K*C+D+1)*L
  nlinarith [mul_nonneg hD (sub_nonneg.mpr hL)]
end OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1_H1_R1_H2_R1
