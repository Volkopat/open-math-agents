import OMAReductions.R_RiemannZetaMoments_moment_isEquiv_83_R1
import Mathlib

/-!
For the balanced approximation to ζ² on the critical line, a pair of indices
first contributes when t reaches 2π times their maximum. Expanding before
integrating gives an ordinary off-diagonal sum and a Gamma-weighted sum.
Both have fixed endpoints for each pair, including pairs at the last cutoff.
-/

open Complex Filter Real MeasureTheory Asymptotics
open scoped ComplexConjugate Topology

namespace OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1_H2_R1

/-- Cancellation between distinct frequencies in the untwisted mean square. -/
def H1 : Prop :=
  let A (n : ℕ) (t : ℝ) :=
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) * (n : ℂ) ^ (-(1/2:ℂ) - I*(t:ℂ))
  (fun T : ℝ => ∑ i ∈ Finset.Icc 1 ⌊T/(2*Real.pi)⌋₊,
    ∑ j ∈ Finset.Icc 1 ⌊T/(2*Real.pi)⌋₊, ∫ t in (max (i:ℝ) j)*(2*Real.pi)..T,
      if i = j then 0 else (A i t * conj (A j t)).re)
    =o[atTop] fun T : ℝ => T * Real.log T ^ 4

/-- Cancellation in the Gamma-weighted square, including equal indices. -/
def H2 : Prop :=
  let A (n : ℕ) (t : ℝ) :=
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) * (n : ℂ) ^ (-(1/2:ℂ) - I*(t:ℂ))
  let q (t : ℝ) := (Gammaℝ (1/2-I*(t:ℂ)) / Gammaℝ (1/2+I*(t:ℂ)))^2
  (fun T : ℝ => ∑ i ∈ Finset.Icc 1 ⌊T/(2*Real.pi)⌋₊,
    ∑ j ∈ Finset.Icc 1 ⌊T/(2*Real.pi)⌋₊, ∫ t in (max (i:ℝ) j)*(2*Real.pi)..T,
      (conj (q t) * A i t * A j t).re)
    =o[atTop] fun T : ℝ => T * Real.log T ^ 4


lemma gammaR_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  simp only [Gammaℝ_def, map_mul]
  have hπ : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) hπ
  simp only [map_div₀, map_neg, map_ofNat, Complex.conj_ofReal] at h
  rw [h]
  congr 1
  simpa only [map_div₀, map_ofNat] using Complex.Gamma_conj (s / 2)

lemma line_conj (t : ℝ) : conj ((1/2 : ℂ) + I*t) = 1/2 - I*t := by
  simp [sub_eq_add_neg, map_ofNat]

lemma line_Gamma_ne (t : ℝ) : Gammaℝ ((1/2 : ℂ) + I*t) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos (by norm_num)

lemma phase_norm (t : ℝ) :
    ‖(Gammaℝ (1/2 - I*(t:ℂ)) / Gammaℝ (1/2 + I*(t:ℂ))) ^ 2‖ = 1 := by
  rw [← line_conj, gammaR_conj, norm_pow, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr (line_Gamma_ne t)), one_pow]

lemma phase_cont : Continuous (fun t : ℝ =>
    (Gammaℝ (1/2 - I*(t:ℂ)) / Gammaℝ (1/2 + I*(t:ℂ))) ^ 2) := by
  have h : Continuous (fun t : ℝ => (Gammaℝ (1/2 + I*(t:ℂ)))⁻¹) :=
    differentiable_Gammaℝ_inv.continuous.comp (by fun_prop)
  have h' : Continuous (fun t : ℝ => Gammaℝ (1/2 + I*(t:ℂ))) := by
    simpa only [Pi.inv_def, inv_inv] using h.inv₀ (fun t => inv_ne_zero (line_Gamma_ne t))
  simp_rw [← line_conj, gammaR_conj]
  exact ((continuous_star.comp h').div h' line_Gamma_ne).pow 2

lemma norm_model_sq (z q : ℂ) (hq : ‖q‖ = 1) :
    ‖z + q * conj z‖ ^ 2 = 2 * ‖z‖ ^ 2 + 2 * ((conj q) * z^2).re := by
  rw [@norm_add_sq ℂ, norm_mul, Complex.norm_conj, hq, one_mul]
  change _ + 2 * ((q * conj z) * conj z).re + _ = _
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

lemma moving_integrable (g : ℕ → ℝ → ℝ) (hg : ∀ n, Continuous (g n))
    {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => g ⌊t / L⌋₊ t) volume 0 T := by
  classical
  let N := ⌊T/L⌋₊
  let piece (j : ℕ) := {t : ℝ | ⌊t/L⌋₊ = j}
  have meas (j) : MeasurableSet (piece j) :=
    (measurableSet_singleton j).preimage
      (Nat.measurable_floor.comp (measurable_id.div_const L))
  have onepiece (j) : IntervalIntegrable ((piece j).indicator (g j)) volume 0 T := by
    rw [intervalIntegrable_iff]
    exact ((hg j).intervalIntegrable (μ := volume) 0 T).1.indicator (meas j) |>
      fun h => by simpa [Set.uIoc_of_le hT] using h
  apply (IntervalIntegrable.sum (Finset.range (N+1)) (fun j _ => onepiece j)).congr
  intro t ht
  have hle : ⌊t/L⌋₊ ≤ N :=
    Nat.floor_mono (div_le_div_of_nonneg_right ((Set.uIoc_of_le hT ▸ ht).2) hL.le)
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem ⌊t/L⌋₊ (Finset.mem_range.mpr (by omega))]
  · simp [piece]
  · intro j _ hne
    exact Set.indicator_of_notMem (s := piece j) (a := t) (fun h => hne (Eq.symm h)) (g j)

lemma term_cont (n : ℕ) (hn : 0 < n) : Continuous (fun t : ℝ =>
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) *
      (n : ℂ) ^ (-(1/2 : ℂ) - I*(t:ℂ))) := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact continuous_const.mul ((by fun_prop :
    Continuous (fun t : ℝ => -(1/2 : ℂ) - I*(t:ℂ))).const_cpow (Or.inl hne))

lemma moving_pair_integral (g : ℕ → ℕ → ℝ → ℝ) (hg : ∀ i ≥ 1, ∀ j ≥ 1, Continuous (g i j))
    {T L : ℝ} (hT : 0 ≤ T) (hL : 0 < L) :
    (∫ t in (0:ℝ)..T, ∑ i ∈ Finset.Icc 1 ⌊t/L⌋₊,
      ∑ j ∈ Finset.Icc 1 ⌊t/L⌋₊, g i j t) =
    ∑ i ∈ Finset.Icc 1 ⌊T/L⌋₊, ∑ j ∈ Finset.Icc 1 ⌊T/L⌋₊,
      ∫ t in (max (i:ℝ) j)*L..T, g i j t := by
  classical
  let S := Finset.Icc 1 ⌊T/L⌋₊
  let start (i j : ℕ) := max (i:ℝ) j * L
  let term (i j : ℕ) := (Set.Ici (start i j)).indicator (g i j)
  have hint (i) (hi : i ∈ S) (j) (hj : j ∈ S) (x y : ℝ) :
      IntervalIntegrable (term i j) volume x y := by
    rw [intervalIntegrable_iff]
    exact ((intervalIntegrable_iff.mp ((hg i (Finset.mem_Icc.mp hi).1 j
      (Finset.mem_Icc.mp hj).1).intervalIntegrable x y)).indicator measurableSet_Ici)
  have fixed (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      (∑ i ∈ Finset.Icc 1 ⌊t/L⌋₊, ∑ j ∈ Finset.Icc 1 ⌊t/L⌋₊, g i j t) =
      ∑ i ∈ S, ∑ j ∈ S, term i j t := by
    have eq : Finset.Icc 1 ⌊t/L⌋₊ = S.filter (fun i : ℕ => (i:ℝ)*L ≤ t) := by
      ext i
      simp only [S, Finset.mem_filter, Finset.mem_Icc,
        Nat.le_floor_iff (div_nonneg ht.1 hL.le), Nat.le_floor_iff (div_nonneg hT hL.le),
        le_div_iff₀ hL]
      exact ⟨fun h => ⟨⟨h.1, h.2.trans ht.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [eq]
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i:ℝ)*L ≤ t
    · rw [if_pos hi]
      apply Finset.sum_congr rfl
      intro j _
      simp [term, start, Set.indicator, max_mul_of_nonneg _ _ hL.le, hi]
    · simp [hi, term, start, max_mul_of_nonneg _ _ hL.le]
  trans ∫ t in (0:ℝ)..T, ∑ i ∈ S, ∑ j ∈ S, term i j t
  · apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hT]
    exact fun t ht => fixed t ht
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum (fun j hj => hint i hi j hj 0 T)]
    apply Finset.sum_congr rfl
    intro j hj
    have hstart : 0 ≤ start i j := mul_nonneg (le_max_of_le_left (Nat.cast_nonneg _)) hL.le
    have hle : start i j ≤ T := by
      apply (le_div_iff₀ hL).mp
      exact max_le ((Nat.le_floor_iff (div_nonneg hT hL.le)).mp (Finset.mem_Icc.mp hi).2)
        ((Nat.le_floor_iff (div_nonneg hT hL.le)).mp (Finset.mem_Icc.mp hj).2)
    have hbefore : (∫ t in (0:ℝ)..start i j, term i j t) = 0 := by
      trans ∫ _ in (0:ℝ)..start i j, (0 : ℝ)
      swap
      · exact intervalIntegral.integral_zero
      apply intervalIntegral.integral_congr_Ioo_of_le hstart
      intro t ht
      exact Set.indicator_of_notMem (not_le.mpr ht.2) _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint i hi j hj 0 (start i j))
      (hint i hi j hj (start i j) T), hbefore, zero_add]
    apply intervalIntegral.integral_congr_Ioo_of_le hle
    intro t ht
    exact Set.indicator_of_mem ht.1.le _
  · intro i hi
    simpa only [← Finset.sum_apply] using IntervalIntegrable.sum S (fun j hj => hint i hi j hj 0 T)


lemma diag_term (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ‖((ArithmeticFunction.sigma 0 n : ℕ):ℂ) * (n : ℂ) ^ (-(1/2:ℂ)-I*(t:ℂ))‖ ^ 2 =
    ((ArithmeticFunction.sigma 0 n : ℕ):ℝ) ^ 2 / (n:ℝ) := by
  rw [norm_mul, mul_pow, Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast]
  have h : (-(1/2:ℂ)-I*(t:ℂ)).re = -(1/2:ℝ) := by norm_num
  rw [h, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  norm_num [div_eq_mul_inv, Real.rpow_neg_one]

lemma expand_square (S : Finset ℕ) (a : ℕ → ℂ) (q : ℂ) :
    let Z := ∑ i ∈ S, a i
    ‖Z‖^2 = (∑ i ∈ S, ‖a i‖^2) +
      (∑ i ∈ S, ∑ j ∈ S, if i = j then 0 else (a i * conj (a j)).re)
    ∧ (conj q * Z^2).re = ∑ i ∈ S, ∑ j ∈ S, (conj q * a i * a j).re := by
  intro Z
  have sq (z : ℂ) : ‖z‖^2 = (z * conj z).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  constructor
  · rw [sq, ← Finset.sum_add_distrib]
    dsimp only [Z]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.add_sum_erase _ _ hi]
    congr 1
    · exact (sq _).symm
    · rw [← Finset.add_sum_erase _ _ hi]
      simp only [ite_true, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj).symm]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
  · simp only [Z, pow_two, ← mul_assoc, Finset.mul_sum, Finset.sum_mul, Complex.re_sum]
    exact Finset.sum_comm

lemma balanced_energy (A : ℕ → ℝ → ℂ) (q : ℝ → ℂ) (b : ℕ → ℝ)
    (hA : ∀ i ≥ 1, Continuous (A i)) (hq : Continuous q) (unit : ∀ t, ‖q t‖ = 1)
    (diagonal : ∀ i ≥ 1, ∀ t, ‖A i t‖^2 = b i) {L T : ℝ} (hL : 0 < L) (hT : 0 ≤ T) :
    let D (t : ℝ) := ∑ i ∈ Finset.Icc 1 ⌊t/L⌋₊, A i t
    let S := Finset.Icc 1 ⌊T/L⌋₊
    (∫ t in (0:ℝ)..T, ‖D t + q t * conj (D t)‖^2) -
      2 * (∫ t in (0:ℝ)..T, ∑ i ∈ Finset.Icc 1 ⌊t/L⌋₊, b i) =
      2 * (∑ i ∈ S, ∑ j ∈ S, ∫ t in (max (i:ℝ) j)*L..T,
        if i = j then 0 else (A i t * conj (A j t)).re) +
      2 * (∑ i ∈ S, ∑ j ∈ S, ∫ t in (max (i:ℝ) j)*L..T,
        (conj (q t) * A i t * A j t).re) := by
  intro D S
  let O (i j : ℕ) (t : ℝ) : ℝ := if i=j then 0 else (A i t * conj (A j t)).re
  let X (i j : ℕ) (t : ℝ) : ℝ := (conj (q t) * A i t * A j t).re
  let block (g : ℕ → ℕ → ℝ → ℝ) (N : ℕ) (t : ℝ) :=
    ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, g i j t
  let cut (t : ℝ) := ⌊t/L⌋₊
  have hO (i : ℕ) (hi : 1 ≤ i) (j : ℕ) (hj : 1 ≤ j) : Continuous (O i j) := by
    by_cases he : i=j
    · simpa [O, he] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    · simp only [O, if_neg he]
      exact continuous_re.comp ((hA i hi).mul (continuous_star.comp (hA j hj)))
  have hX (i : ℕ) (hi : 1 ≤ i) (j : ℕ) (hj : 1 ≤ j) : Continuous (X i j) :=
    continuous_re.comp (((continuous_star.comp hq).mul (hA i hi)).mul (hA j hj))
  have hint (g : ℕ → ℕ → ℝ → ℝ) (hg : ∀ i ≥ 1, ∀ j ≥ 1, Continuous (g i j)) :
      IntervalIntegrable (fun t => block g (cut t) t) volume 0 T := by
    apply moving_integrable _ _ hL hT
    intro N
    exact continuous_finsetSum _ (fun i hi => continuous_finsetSum _
      (fun j hj => hg i (Finset.mem_Icc.mp hi).1 j (Finset.mem_Icc.mp hj).1))
  let B (t : ℝ) := ∑ i ∈ Finset.Icc 1 (cut t), b i
  have hb : IntervalIntegrable B volume 0 T :=
    moving_integrable (fun N _ => ∑ i ∈ Finset.Icc 1 N, b i) (fun _ => continuous_const) hL hT
  have eq (t : ℝ) : ‖D t + q t * conj (D t)‖^2 =
      2*B t + 2*block O (cut t) t + 2*block X (cut t) t := by
    obtain ⟨h₁,h₂⟩ := expand_square (Finset.Icc 1 (cut t)) (fun i => A i t) (q t)
    rw [norm_model_sq _ _ (unit t)]
    change 2 * ‖∑ i ∈ Finset.Icc 1 (cut t), A i t‖^2 +
      2 * (conj (q t) * (∑ i ∈ Finset.Icc 1 (cut t), A i t)^2).re = _
    rw [h₁,h₂]
    have bd : (∑ i ∈ Finset.Icc 1 (cut t), ‖A i t‖^2) = B t :=
      Finset.sum_congr rfl (fun i hi => diagonal i (Finset.mem_Icc.mp hi).1 t)
    rw [bd]
    dsimp only [block,O,X]
    ring
  change (∫ t in (0:ℝ)..T, _) - 2*(∫ t in (0:ℝ)..T, B t) = _
  simp_rw [eq]
  rw [intervalIntegral.integral_add ((hb.const_mul 2).add ((hint O hO).const_mul 2))
      ((hint X hX).const_mul 2),
    intervalIntegral.integral_add (hb.const_mul 2) ((hint O hO).const_mul 2)]
  simp only [intervalIntegral.integral_const_mul]
  rw [show (∫ t in (0:ℝ)..T, block O (cut t) t) = _ from moving_pair_integral O hO hT hL,
    show (∫ t in (0:ℝ)..T, block X (cut t) t) = _ from moving_pair_integral X hX hT hL]
  dsimp only [O,X,S]
  ring


theorem main : H1 → H2 → OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1.H2 := by
  let A (n : ℕ) (t : ℝ) :=
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) * (n : ℂ) ^ (-(1/2:ℂ) - I*(t:ℂ))
  let q (t : ℝ) := (Gammaℝ (1/2-I*(t:ℂ)) / Gammaℝ (1/2+I*(t:ℂ)))^2
  let O := (fun T : ℝ => ∑ i ∈ Finset.Icc 1 ⌊T/(2*Real.pi)⌋₊,
    ∑ j ∈ Finset.Icc 1 ⌊T/(2*Real.pi)⌋₊, ∫ t in (max (i:ℝ) j)*(2*Real.pi)..T,
      if i = j then 0 else (A i t * conj (A j t)).re)
  let X := (fun T : ℝ => ∑ i ∈ Finset.Icc 1 ⌊T/(2*Real.pi)⌋₊,
    ∑ j ∈ Finset.Icc 1 ⌊T/(2*Real.pi)⌋₊, ∫ t in (max (i:ℝ) j)*(2*Real.pi)..T,
      (conj (q t) * A i t * A j t).re)
  intro ordinary twisted
  change O =o[atTop] _ at ordinary
  change X =o[atTop] _ at twisted
  have combined := (ordinary.const_mul_left 2).add (twisted.const_mul_left 2)
  apply combined.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (balanced_energy A q (fun i => ((ArithmeticFunction.sigma 0 i : ℕ):ℝ)^2 / i)
    term_cont phase_cont phase_norm diag_term (by positivity) hT).symm

end OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1_H2_R1
