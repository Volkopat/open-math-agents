import OMAReductions.R_Green92_green_92_variants_chase_upper_R1_H1_R1
import Mathlib

/-! The midpoint of the means separates the two trace distributions. -/

open Finset MeasureTheory ProbabilityTheory
open scoped Classical NNReal
open Green92

private noncomputable def mean {A : Type*} [Fintype A] (g : A → ℝ) : ℝ :=
  (∑ w, g w) / Fintype.card A

private theorem upperTail {A : Type*} [Fintype A] [Nonempty A]
    {m : ℕ} (hm : 0 < m) (g : A → ℝ) (l : ℝ)
    (hg : ∀ w, l ≤ g w ∧ g w ≤ l + 1) {a : ℝ} (ha : 0 ≤ a) :
    ((univ.filter fun S : Fin m → A =>
        (m : ℝ) * a / 2 ≤ ∑ i, (g (S i) - mean g)).card : ℝ) ≤
      (Fintype.card (Fin m → A) : ℝ) * Real.exp (-(m : ℝ) * a^2 / 8) := by
  let : MeasurableSpace A := ⊤
  let μ := uniformOn (Set.univ : Set A)
  let ν := Measure.pi (fun _ : Fin m => μ)
  let X : Fin m → (Fin m → A) → ℝ := fun i S => g (S i) - mean g
  have hmean : (∫ w, g w ∂μ) = mean g := by
    rw [integral_fintype]
    · simp [μ, uniformOn_univ, Measure.real_def, mean, div_eq_mul_inv]
      rw [← Finset.mul_sum, mul_comm]
    · exact Integrable.of_mem_Icc l (l+1) Measurable.of_discrete.aemeasurable
        (Filter.Eventually.of_forall hg)
  have hsub : HasSubgaussianMGF (fun w => g w - mean g) ((1 : ℝ≥0) / 4) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := g) Measurable.of_discrete.aemeasurable
      (Filter.Eventually.of_forall hg)
    rw [hmean, add_sub_cancel_left] at h
    convert h using 1
    norm_num
  have hi : iIndepFun X ν := by
    exact iIndepFun_pi (X := fun _ : Fin m => fun w : A => g w - mean g)
      (fun _ => Measurable.of_discrete.aemeasurable)
  have hs (i : Fin m) : HasSubgaussianMGF (X i) ((1 : ℝ≥0) / 4) ν := by
    have hi' : MeasurePreserving (Function.eval i) ν μ :=
      measurePreserving_eval (μ := fun _ : Fin m => μ) i
    apply HasSubgaussianMGF.of_map (X := fun w => g w - mean g) hi'.measurable.aemeasurable
    rwa [hi'.map_eq]
  have hb := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi
    (s := Finset.univ) (fun i _ => hs i) (ε := (m : ℝ) * a / 2) (by positivity)
  have hν : ν = uniformOn (Set.univ : Set (Fin m → A)) := by
    simpa [ν, μ] using (uniformOn_pi (f := fun _ : Fin m => (Set.univ : Set A))).symm
  let E := univ.filter (fun S : Fin m → A => (m : ℝ) * a / 2 ≤ ∑ i, X i S)
  have hE : (E : Set (Fin m → A)) = {S | (m : ℝ) * a / 2 ≤ ∑ i, X i S} := by
    ext S
    simp [E]
  have hprob : ν.real (E : Set (Fin m → A)) = (E.card : ℝ) / Fintype.card (Fin m → A) := by
    rw [hν, Measure.real_def, uniformOn_univ, Measure.count_apply_finset,
      ENNReal.toReal_div]
    simp
  rw [← hE, hprob] at hb
  have hcard : 0 < (Fintype.card (Fin m → A) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hmr : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have harg : -((m : ℝ) * a / 2)^2 / (2 * ((m : ℝ) * (1/4))) =
      -(m : ℝ) * a^2 / 2 := by
    field_simp
    ring
  have hexp : Real.exp (-(m : ℝ) * a^2 / 2) ≤ Real.exp (-(m : ℝ) * a^2 / 8) := by
    apply Real.exp_le_exp.mpr
    linarith [mul_nonneg hmr.le (sq_nonneg a)]
  have hb' : (E.card : ℝ) / Fintype.card (Fin m → A) ≤
      Real.exp (-(m : ℝ) * a^2 / 2) := by
    convert hb using 1
    rw [← harg]
    congr 1
    simp [Finset.sum_const, nsmul_eq_mul]
  simpa [E, X, mul_comm] using (div_le_iff₀ hcard).mp (hb'.trans hexp)

private theorem traceConcentration (n m : ℕ) (x y : Fin n → Bool)
    (F : List Bool → ℝ) (a : ℝ)
    (hm : 0 < m) (ha : 0 < a) (_ : a ≤ 1) (hF : ∀ w, 0 ≤ F w ∧ F w ≤ 1)
    (hgap : a * Fintype.card (Finset (Fin n)) ≤
      (∑ S : Finset (Fin n), F (trace x S)) - ∑ S : Finset (Fin n), F (trace y S)) :
    ∃ T : (Fin m → List Bool) → Prop,
      let b := (Fintype.card (Fin m → Finset (Fin n)) : ℝ) * Real.exp (-(m:ℝ)*a^2/8)
      ((univ.filter fun S : Fin m → Finset (Fin n) => ¬T (fun i => trace x (S i))).card : ℝ) ≤ b ∧
      ((univ.filter fun S : Fin m → Finset (Fin n) => T (fun i => trace y (S i))).card : ℝ) ≤ b := by
  let A := Finset (Fin n)
  let gx : A → ℝ := fun S => F (trace x S)
  let gy : A → ℝ := fun S => F (trace y S)
  let b := (m : ℝ) * (mean gx + mean gy) / 2
  have hcard : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsep : a ≤ mean gx - mean gy := by
    rw [mean, mean, ← sub_div, le_div_iff₀ hcard]
    exact hgap
  have hscaled := mul_le_mul_of_nonneg_left hsep (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hneg : mean (fun S => -gx S) = -mean gx := by
    simp [mean, Finset.sum_neg_distrib, neg_div]
  have hx : ∀ S, (-1 : ℝ) ≤ -gx S ∧ -gx S ≤ -1 + 1 := fun S => by
    have h := hF (trace x S)
    dsimp [gx]
    constructor <;> linarith [h.1, h.2]
  have hy : ∀ S, (0 : ℝ) ≤ gy S ∧ gy S ≤ 0 + 1 := fun S => by
    simpa [gy] using hF (trace y S)
  refine ⟨fun w => b ≤ ∑ i, F (w i), ?_, ?_⟩
  · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (upperTail hm _ (-1) hx ha.le)
    intro S hS
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsum : (∑ i : Fin m, gx (S i)) < b := lt_of_not_ge hS.2
    simp only [hneg, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [b] at hsum
    nlinarith
  · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (upperTail hm _ 0 hy ha.le)
    intro S hS
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsum : b ≤ (∑ i : Fin m, gy (S i)) := hS.2
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    dsimp [b] at hsum
    nlinarith

theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_upper_R1_H1_R1.H2 := traceConcentration