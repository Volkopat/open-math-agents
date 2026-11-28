import OMAStatements.S_mo_142880
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Basic

-- A conditional reduction to independent discrete and continuous tail estimates.
-- The deterministic translation comparison is proved below. Both signed tails
-- are essential; the probabilistic estimates are not claimed as proved here.
namespace OMA.R_mo_142880_R1

open MeasureTheory ProbabilityTheory

def H1 : Prop :=
  ∀ d : ℝ, 0 < d →
    let q : ℝ → ℝ := fun x => Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)
    ∃ c C R : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ R ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ D : Ω → ℤ, AEMeasurable D P →
          (∀ᵐ ω ∂P, ∀ t : ℤ,
            OMA.S_mo_142880.height B d t ω ≤ OMA.S_mo_142880.height B d (D ω) ω) →
          ∀ x : ℝ, R ≤ x →
            P.real {ω | x < (D ω : ℝ)} ≤ C * q x ∧
            c * q x ≤ 1 - P.real {ω | -x < (D ω : ℝ)}


def H2 : Prop :=
  ∀ d : ℝ, 0 < d →
    let q : ℝ → ℝ := fun x => Real.exp (-(d ^ 2 / 2) * x) / (1 + x) ^ ((3 : ℝ) / 2)
    ∃ c C R : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ R ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ → Ω → ℝ),
        IsBrownianReal (fun t : NNReal => B (t : ℝ)) P →
        IsBrownianReal (fun t : NNReal => B (-(t : ℝ))) P →
        IndepFun (fun ω (t : NNReal) => B (t : ℝ) ω)
          (fun ω (t : NNReal) => B (-(t : ℝ)) ω) P →
        ∀ T : Ω → ℝ, AEMeasurable T P →
          (∀ᵐ ω ∂P, ∀ t : ℝ,
            OMA.S_mo_142880.height B d t ω ≤ OMA.S_mo_142880.height B d (T ω) ω) →
          ∀ x : ℝ, R ≤ x →
            c * q x ≤ P.real {ω | x < T ω} ∧
            1 - P.real {ω | -x < T ω} ≤ C * q x

lemma exists_exponential_scale (rate CF cG CG cF : ℝ)
    (hrate : 0 < rate) (hCF : 0 < CF) (hcG : 0 < cG) (hCG : 0 < CG) (hcF : 0 < cF) :
    ∃ s : ℝ, 0 ≤ s ∧ CF * Real.exp (-rate * s) ≤ cG ∧ CG * Real.exp (-rate * s) ≤ cF := by
  let t := min (cG / CF) (cF / CG)
  have ht : 0 < t := lt_min (div_pos hcG hCF) (div_pos hcF hCG)
  let s := max 0 (-Real.log t / rate)
  have hs : 0 ≤ s := le_max_left _ _
  have hsl : -Real.log t / rate ≤ s := le_max_right _ _
  have hmul : -Real.log t ≤ s * rate := (div_le_iff₀ hrate).mp hsl
  have he : Real.exp (-rate * s) ≤ t := by
    calc
      _ ≤ Real.exp (Real.log t) := Real.exp_le_exp.mpr (by nlinarith)
      _ = t := Real.exp_log ht
  refine ⟨s, hs, ?_, ?_⟩
  · have h := (le_div_iff₀ hCF).mp (he.trans (min_le_left _ _))
    simpa only [mul_comm] using h
  · have h := (le_div_iff₀ hCG).mp (he.trans (min_le_right _ _))
    simpa only [mul_comm] using h

lemma survival_comparison_at_shift
    (F G q : ℝ → ℝ) (R rate cF CF cG CG s : ℝ)
    (hFanti : Antitone F) (hGanti : Antitone G)
    (hR : 0 ≤ R) (hrate : 0 < rate)
    (_hcF : 0 < cF) (hCF : 0 < CF) (_hcG : 0 < cG) (hCG : 0 < CG)
    (hq : ∀ x : ℝ, R ≤ x → 0 ≤ q x)
    (hshift : ∀ x t : ℝ, R ≤ x → 0 ≤ t →
      q (x + t) ≤ Real.exp (-rate * t) * q x)
    (hF : ∀ x : ℝ, R ≤ x →
      F x ≤ CF * q x ∧ cF * q x ≤ 1 - F (-x))
    (hG : ∀ x : ℝ, R ≤ x →
      cG * q x ≤ G x ∧ 1 - G (-x) ≤ CG * q x)
    (hs : 0 ≤ s)
    (hCFs : CF * Real.exp (-rate * s) ≤ cG)
    (hCGs : CG * Real.exp (-rate * s) ≤ cF) :
    ∀ x : ℝ, F x ≤ G (x - 2 * (R + s)) := by
  let b := 2 * (R + s)
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hbs : s ≤ b := by dsimp [b]; linarith
  have he : Real.exp (-rate * b) ≤ Real.exp (-rate * s) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hCFb : CF * Real.exp (-rate * b) ≤ cG :=
    (mul_le_mul_of_nonneg_left he hCF.le).trans hCFs
  have hCGb : CG * Real.exp (-rate * b) ≤ cF :=
    (mul_le_mul_of_nonneg_left he hCG.le).trans hCGs
  have hRs : R ≤ R + s := by linarith
  have hqR : 0 ≤ q R := hq R le_rfl
  have hsmallG : CG * q (R + s) ≤ cF * q R := by
    calc
      _ ≤ CG * (Real.exp (-rate * s) * q R) :=
        mul_le_mul_of_nonneg_left (hshift R s le_rfl hs) hCG.le
      _ = (CG * Real.exp (-rate * s)) * q R := by ring
      _ ≤ cF * q R := mul_le_mul_of_nonneg_right hCGs hqR
  have hsmallF : CF * q (R + s) ≤ cG * q R := by
    calc
      _ ≤ CF * (Real.exp (-rate * s) * q R) :=
        mul_le_mul_of_nonneg_left (hshift R s le_rfl hs) hCF.le
      _ = (CF * Real.exp (-rate * s)) * q R := by ring
      _ ≤ cG * q R := mul_le_mul_of_nonneg_right hCFs hqR
  have hmiddleLeft : F (-R) ≤ G (-(R + s)) := by
    have hFl := (hF R le_rfl).2
    have hGl := (hG (R + s) hRs).2
    linarith
  have hmiddleRight : F (R + s) ≤ G R :=
    ((hF (R + s) hRs).1.trans hsmallF).trans (hG R le_rfl).1
  intro x
  change F x ≤ G (x - b)
  by_cases hleft : x ≤ -R
  · have hz : R ≤ -x := by linarith
    have hzb : R ≤ -x + b := by linarith
    have hFl : cF * q (-x) ≤ 1 - F x := by
      simpa only [neg_neg] using (hF (-x) hz).2
    have hGl := (hG (-x + b) hzb).2
    have hneg : -(-x + b) = x - b := by ring
    rw [hneg] at hGl
    have hqstep : CG * q (-x + b) ≤ cF * q (-x) := by
      calc
        _ ≤ CG * (Real.exp (-rate * b) * q (-x)) :=
          mul_le_mul_of_nonneg_left (hshift (-x) b hz hb) hCG.le
        _ = (CG * Real.exp (-rate * b)) * q (-x) := by ring
        _ ≤ cF * q (-x) := mul_le_mul_of_nonneg_right hCGb (hq (-x) hz)
    linarith
  · by_cases hright : b + R ≤ x
    · have hz : R ≤ x - b := by linarith
      have hFx := (hF x (by linarith)).1
      have hGy := (hG (x - b) hz).1
      have hqstep : CF * q x ≤ cG * q (x - b) := by
        have hp := hshift (x - b) b hz hb
        rw [sub_add_cancel] at hp
        calc
          _ ≤ CF * (Real.exp (-rate * b) * q (x - b)) :=
            mul_le_mul_of_nonneg_left hp hCF.le
          _ = (CF * Real.exp (-rate * b)) * q (x - b) := by ring
          _ ≤ cG * q (x - b) := mul_le_mul_of_nonneg_right hCFb (hq (x - b) hz)
      exact (hFx.trans hqstep).trans hGy
    · by_cases hmid : x ≤ R + s
      · have hFx : F x ≤ F (-R) := hFanti (by linarith)
        have hGy : G (-(R + s)) ≤ G (x - b) := hGanti (by dsimp [b]; linarith)
        exact (hFx.trans hmiddleLeft).trans hGy
      · have hFx : F x ≤ F (R + s) := hFanti (by linarith)
        have hGy : G R ≤ G (x - b) := hGanti (by linarith)
        exact (hFx.trans hmiddleRight).trans hGy

lemma exists_survival_shift
    (F G q : ℝ → ℝ) (R rate cF CF cG CG : ℝ)
    (hFanti : Antitone F) (hGanti : Antitone G)
    (hR : 0 ≤ R) (hrate : 0 < rate)
    (hcF : 0 < cF) (hCF : 0 < CF) (hcG : 0 < cG) (hCG : 0 < CG)
    (hq : ∀ x : ℝ, R ≤ x → 0 ≤ q x)
    (hshift : ∀ x t : ℝ, R ≤ x → 0 ≤ t →
      q (x + t) ≤ Real.exp (-rate * t) * q x)
    (hF : ∀ x : ℝ, R ≤ x →
      F x ≤ CF * q x ∧ cF * q x ≤ 1 - F (-x))
    (hG : ∀ x : ℝ, R ≤ x →
      cG * q x ≤ G x ∧ 1 - G (-x) ≤ CG * q x) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ x : ℝ, F x ≤ G (x - b) := by
  obtain ⟨s, hs, hCFs, hCGs⟩ := exists_exponential_scale rate CF cG CG cF hrate hCF hcG hCG hcF
  refine ⟨2 * (R + s), by linarith, ?_⟩
  exact survival_comparison_at_shift F G q R rate cF CF cG CG s hFanti hGanti hR hrate
    hcF hCF hcG hCG hq hshift hF hG hs hCFs hCGs

lemma q_pos (a x : ℝ) (hx : 0 ≤ x) : 0 < (Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)) := by
  apply div_pos (Real.exp_pos _)
  exact Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + x) _

lemma q_shift_le (a x s : ℝ) (hx : 0 ≤ x) (hs : 0 ≤ s) :
    (Real.exp (-a * (x + s)) / (1 + (x + s)) ^ ((3 : ℝ) / 2)) ≤ Real.exp (-a * s) * (Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)) := by
  have hden : 0 < (1 + x) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + x) _
  have hmono : (1 + x) ^ ((3 : ℝ) / 2) ≤ (1 + (x + s)) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 1 + x) (by linarith) (by norm_num)
  calc
    _ = Real.exp (-a * s) *
        (Real.exp (-a * x) / (1 + (x + s)) ^ ((3 : ℝ) / 2)) := by
      rw [show -a * (x + s) = -a * s + -a * x by ring, Real.exp_add, mul_div_assoc]
    _ ≤ Real.exp (-a * s) *
        (Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hden hmono

lemma q_shift_le_above (a x R s : ℝ) (hR : 0 ≤ R) (hx : R ≤ x) (hs : 0 ≤ s) :
    (Real.exp (-a * (x + s)) / (1 + (x + s)) ^ ((3 : ℝ) / 2)) ≤ Real.exp (-a * s) * (Real.exp (-a * x) / (1 + x) ^ ((3 : ℝ) / 2)) :=
  q_shift_le a x s (hR.trans hx) hs

theorem main : H1 → H2 → type_of% @OMA.S_mo_142880.main := by
  intro h₁ h₂ d hd
  obtain ⟨cF, CF, RF, hcF, hCF, hRF, hD⟩ := h₁ d hd
  obtain ⟨cG, CG, RG, hcG, hCG, hRG, hT⟩ := h₂ d hd
  let R := max RF RG
  let rate : ℝ := d ^ 2 / 2
  let q : ℝ → ℝ := fun x => Real.exp (-rate * x) / (1 + x) ^ ((3 : ℝ) / 2)
  have hR : 0 ≤ R := hRF.trans (le_max_left _ _)
  have hrate : 0 < rate := by dsimp [rate]; nlinarith [mul_pos hd hd]
  obtain ⟨s, hs, hCFs, hCGs⟩ := exists_exponential_scale rate CF cG CG cF hrate hCF hcG hCG hcF
  let b := 2 * (R + s)
  refine ⟨1, b, by norm_num, ?_⟩
  intro Ω mΩ P hP B hBp hBn hind D T hDmeas hTmeas hDmax hTmax x
  let F : ℝ → ℝ := fun t => P.real {ω | t < (D ω : ℝ)}
  let G : ℝ → ℝ := fun t => P.real {ω | t < T ω}
  have hFanti : Antitone F := by
    intro u v huv
    exact measureReal_mono (by intro ω hω; exact lt_of_le_of_lt huv hω)
  have hGanti : Antitone G := by
    intro u v huv
    exact measureReal_mono (by intro ω hω; exact lt_of_le_of_lt huv hω)
  have hDf := hD Ω P B hBp hBn hind D hDmeas hDmax
  have hTf := hT Ω P B hBp hBn hind T hTmeas hTmax
  have hq : ∀ t : ℝ, R ≤ t → 0 ≤ q t := by
    intro t ht
    exact (q_pos rate t (hR.trans ht)).le
  have hshift : ∀ t u : ℝ, R ≤ t → 0 ≤ u →
      q (t + u) ≤ Real.exp (-rate * u) * q t := by
    intro t u ht hu
    exact q_shift_le rate t u (hR.trans ht) hu
  have hF : ∀ t : ℝ, R ≤ t →
      F t ≤ CF * q t ∧ cF * q t ≤ 1 - F (-t) := by
    intro t ht
    exact hDf t ((le_max_left RF RG).trans ht)
  have hG : ∀ t : ℝ, R ≤ t →
      cG * q t ≤ G t ∧ 1 - G (-t) ≤ CG * q t := by
    intro t ht
    exact hTf t ((le_max_right RF RG).trans ht)
  have hx := survival_comparison_at_shift F G q R rate cF CF cG CG s
    hFanti hGanti hR hrate hcF hCF hcG hCG hq hshift hF hG hs hCFs hCGs x
  have hxReal : P.real {ω | x < (D ω : ℝ)} ≤ P.real {ω | x - b < T ω} := hx
  have hxMeasure : P {ω | x < (D ω : ℝ)} ≤ P {ω | x - b < T ω} := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mp
    simpa only [measureReal_def] using hxReal
  simpa only [one_mul, sub_lt_iff_lt_add] using hxMeasure

end OMA.R_mo_142880_R1
