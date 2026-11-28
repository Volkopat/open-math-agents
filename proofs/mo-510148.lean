import OMAStatements.S_mo_510148
import Mathlib

open OMA.S_mo_510148 MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

private noncomputable def sign (b : Bool) : ℝ := if b then 1 else -1

private theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

private theorem finite_memLp {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) :
    MemLp f 2 μ :=
  (memLp_top_of_bound (measurable_of_countable f).aestronglyMeasurable
    (∑ x, ‖f x‖) (Filter.Eventually.of_forall fun x =>
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ x))).mono_exponent le_top

private theorem counterexample : ¬ (type_of% @OMA.S_mo_510148.main.{u}) := by
  classical
  intro h
  obtain ⟨C, hC, hbound⟩ := h 1 1 2 2 (by norm_num) (by norm_num) le_rfl
  let m : ℕ := ⌈C⌉₊ + 2
  let n : ℕ := m ^ 2
  let r : ℝ := m
  have hrC : C < r := by
    have hc := Nat.le_ceil C
    dsimp [r, m]
    push_cast
    linarith
  have hr : 0 < r := hC.trans_lt hrC
  have hn : 0 < n := by dsimp [n, m]; positivity
  have hn2 : 2 ≤ n := (by decide : 2 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left (by dsimp [m]; omega) _)
  have hnr : (n : ℝ) = r ^ 2 := by simp [n, r]
  let i₀ : Fin n := ⟨0, hn⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  let Ω := Fin n → ULift.{u} Bool
  let ν : Measure (ULift.{u} Bool) := (PMF.uniformOfFintype (ULift.{u} Bool)).toMeasure
  let μ : Measure Ω := Measure.pi (fun _ : Fin n => ν)
  let : IsProbabilityMeasure μ := by dsimp [μ, ν]; infer_instance
  let X : Fin n → Ω → ℝ := fun i ω => sign (ω i).down
  have hXmeas (i : Fin n) : Measurable (X i) := measurable_of_countable _
  have hInd : iIndepFun X μ :=
    iIndepFun_pi (fun _ => (measurable_of_countable (sign ∘ ULift.down)).aemeasurable)
  have hXmean (i : Fin n) : (∫ ω, X i ω ∂μ) = 0 := by
    have hp := measurePreserving_eval (fun _ : Fin n => ν) i
    change (∫ ω : Ω, sign (ω i).down ∂μ) = 0
    have hpInt : (∫ ω : Ω, sign (ω i).down ∂μ) = ∫ b, sign b.down ∂ν := by
      exact (hp.map_eq ▸ integral_map (μ := μ) hp.measurable.aemeasurable
        (measurable_of_countable (sign ∘ ULift.down)).aestronglyMeasurable).symm
    rw [hpInt]
    rw [integral_fintype Integrable.of_finite]
    rw [← Equiv.sum_comp (Equiv.ulift.symm : Bool ≃ ULift.{u} Bool)]
    norm_num [measureReal_def, ν, PMF.toMeasure_apply_singleton,
      PMF.uniformOfFintype_apply, Fintype.sum_bool, sign]
  have hXvar (i : Fin n) : variance (X i) μ = 1 := by
    rw [variance_of_integral_eq_zero (hXmeas i).aemeasurable (hXmean i)]
    simp [X, sign_sq]
  have hX : ∀ i : Fin n, Measurable (X i) ∧ (∫ ω, X i ω ∂μ) = 0 ∧
      (∀ᵐ ω ∂μ, |X i ω| ≤ 1) ∧ 1 ≤ variance (X i) μ := by
    intro i
    refine ⟨hXmeas i, hXmean i, Filter.Eventually.of_forall ?_, (hXvar i).ge⟩
    intro ω
    change |sign (ω i).down| ≤ 1
    cases (ω i).down <;> norm_num [sign]
  let R : Ω → ℝ := fun ω => X i₀ ω * X i₁ ω
  have hRmean : (∫ ω, R ω ∂μ) = 0 := by
    have hcov := (hInd.indepFun hne).covariance_eq_zero
      (finite_memLp μ (X i₀)) (finite_memLp μ (X i₁))
    rw [covariance_eq_sub (finite_memLp μ (X i₀)) (finite_memLp μ (X i₁)),
      hXmean, hXmean, zero_mul, sub_zero] at hcov
    exact hcov
  have hRsq (ω : Ω) : R ω ^ 2 = 1 := by
    simp [R, X, mul_pow, sign_sq]
  let a : Option (Fin 1) → Fin n → ℝ := fun j i =>
    (if i = i₀ then r else 0) + (if i = i₁ then (if j = none then -r else r) else 0)
  let Y : Option (Fin 1) → Ω → ℝ := fun j ω => ∑ i, a j i * X i ω
  let L : Ω → ℝ := Y none
  let P : Ω → Fin 1 → ℝ := fun ω j => Y (some j) ω
  have hL (ω : Ω) : L ω = r * X i₀ ω - r * X i₁ ω := by
    simp [L, Y, a, add_mul, Finset.sum_add_distrib, ite_mul, sub_eq_add_neg]
  have hP (ω : Ω) (j : Fin 1) : P ω j = r * X i₀ ω + r * X i₁ ω := by
    simp [P, Y, a, add_mul, Finset.sum_add_distrib, ite_mul]
  have hlinear (b d : ℝ) : (∫ ω, b * X i₀ ω + d * X i₁ ω ∂μ) = 0 := by
    rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
      integral_const_mul, hXmean, hXmean]
    ring
  have hbracket : CovarianceBracket μ n 2 2 Y := by
    intro u
    let B := u none
    let D := u (some 0)
    have hu (ω : Ω) : (∑ j, u j * Y j ω) =
        (B + D) * r * X i₀ ω + (D - B) * r * X i₁ ω := by
      rw [Fintype.sum_option, Fin.sum_univ_one]
      change B * L ω + D * P ω 0 = _
      rw [hL, hP]
      ring
    have hmean : (∫ ω, ∑ j, u j * Y j ω ∂μ) = 0 := by
      simp_rw [hu]
      exact hlinear _ _
    have hsquare (ω : Ω) : (∑ j, u j * Y j ω) ^ 2 =
        (2 * (n : ℝ) * (B ^ 2 + D ^ 2)) +
        (2 * (n : ℝ) * (B + D) * (D - B)) * R ω := by
      rw [hu, hnr]
      calc
        _ = r ^ 2 * (B+D)^2 * (X i₀ ω)^2 + r ^ 2 * (D-B)^2 * (X i₁ ω)^2 +
            (2*r^2*(B+D)*(D-B)) * R ω := by dsimp [R]; ring
        _ = _ := by simp [X, sign_sq]; ring
    have hv : variance (fun ω => ∑ j, u j * Y j ω) μ =
        2 * (n : ℝ) * (B ^ 2 + D ^ 2) := by
      rw [variance_of_integral_eq_zero (measurable_of_countable _).aemeasurable hmean]
      simp_rw [hsquare]
      rw [integral_add Integrable.of_finite Integrable.of_finite]
      rw [integral_const, integral_const_mul _ R, hRmean]
      simp
    change 2 * (∑ j, u j ^ 2) ≤ variance (fun ω => ∑ j, u j * Y j ω) μ / (n : ℝ) ∧ _
    have hs : 2 * (∑ j, u j ^ 2) =
        variance (fun ω => ∑ j, u j * Y j ω) μ / (n : ℝ) := by
      rw [Fintype.sum_option, Fin.sum_univ_one, hv]
      dsimp [B, D]
      field_simp [(by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
    exact ⟨hs.le, hs.ge⟩
  have hLmean : (∫ ω, L ω ∂μ) = 0 := by simpa only [hL, sub_eq_add_neg, neg_mul] using hlinear r (-r)
  have horth (j : Fin 1) : covariance L (fun ω => P ω j) μ = 0 := by
    rw [covariance_eq_sub (finite_memLp μ L) (finite_memLp μ (fun ω => P ω j)), hLmean]
    have hzero (ω : Ω) : L ω * P ω j = 0 := by
      rw [hL, hP]
      calc
        _ = r ^ 2 * ((X i₀ ω)^2 - (X i₁ ω)^2) := by ring
        _ = 0 := by simp [X, sign_sq]
    simp [Pi.mul_apply, hzero]
  let f : (Fin 1 → ℝ) → ℝ := fun z => if z 0 = 0 then -1 else 1
  have hf : Measurable f :=
    Measurable.ite ((measurable_pi_apply 0) (measurableSet_singleton 0))
      measurable_const measurable_const
  have hF : f ∘ P = R := by
    funext ω
    change f (P ω) = R ω
    change (if P ω 0 = 0 then (-1 : ℝ) else 1) = R ω
    rw [hP]
    rcases h₀ : (ω i₀).down with _ | _ <;> rcases h₁ : (ω i₁).down with _ | _ <;>
      simp [R, X, sign, h₀, h₁, hr.ne']
  let Z : Ω → ℝ := fun ω => L ω ^ 2
  have hZ (ω : Ω) : Z ω = 2 * (n : ℝ) - (2 * (n : ℝ)) * R ω := by
    dsimp [Z]
    rw [hL, hnr]
    calc
      _ = r ^ 2 * ((X i₀ ω)^2 + (X i₁ ω)^2 - 2 * R ω) := by dsimp [R]; ring
      _ = _ := by simp [X, sign_sq]; ring
  have hRvar : variance R μ = 1 := by
    rw [variance_of_integral_eq_zero (measurable_of_countable _).aemeasurable hRmean]
    simp [hRsq]
  have hZvar : variance Z μ = (2 * (n : ℝ)) ^ 2 := by
    rw [show Z = (fun ω => 2 * (n : ℝ) - 2 * (n : ℝ) * R ω) from funext hZ]
    rw [variance_const_sub (measurable_of_countable _).aestronglyMeasurable,
      variance_const_mul, hRvar, mul_one]
  have hZR : covariance Z R μ = -(2 * (n : ℝ)) := by
    rw [covariance_eq_sub (finite_memLp μ Z) (finite_memLp μ R), hRmean, mul_zero, sub_zero]
    have he (ω : Ω) : Z ω * R ω = (2 * (n : ℝ)) * R ω - (2 * (n : ℝ)) := by
      rw [hZ]
      linear_combination -(2 * (n : ℝ)) * hRsq ω
    simp_rw [Pi.mul_apply, he]
    rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul, hRmean]
    simp
  have hb := hbound n hn Ω μ X a hInd hX hbracket horth f hf
    ⟨1, fun z => by dsimp [f]; split <;> norm_num⟩
    (by change (∫ ω, (f ∘ P) ω ∂μ) = 0; rw [hF, hRmean]) 2 (Or.inr rfl)
  change |covariance Z (f ∘ P) μ| ≤
    C * Real.sqrt (variance Z μ) * Real.sqrt (∫ ω, (f ∘ P) ω ^ 2 ∂μ) / Real.sqrt (n : ℝ) at hb
  rw [hF, hZR, hZvar, abs_neg, abs_of_nonneg (by positivity),
    Real.sqrt_sq (by positivity), hnr, Real.sqrt_sq hr.le] at hb
  simp [hRsq, integral_const] at hb
  have hpos : 0 < 2 * r ^ 2 := by positivity
  have hle : r ≤ C := (mul_le_mul_iff_right₀ hpos).mp (by
    have hh := (le_div_iff₀ hr).mp hb
    simpa only [mul_comm, mul_assoc, mul_left_comm] using hh)
  exact hrC.not_ge hle

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_510148.main) := counterexample