import OMAReductions.R_Erdos727_erdos_727_variants_k_2_R1
import Mathlib

/-!
The quadratic family is due to Rexyysilent's candidate for Erdős 727, k = 2.
We work on a fixed factorial progression, establish uniform quadratic
cancellation by averaging spaced translates, and count carry failures at
levels starting with p³. The reciprocal-prime estimates below adapt work by
Marcus Buffett and senamakel from the merged Erdős 1100 normal-order proof.
-/

namespace OMA.QuadraticCarry

open Finset Complex
open scoped BigOperators

noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

@[local simp] lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  rw [phase, Complex.ofReal_add, add_mul, Complex.exp_add, phase, phase]

lemma phase_nat_mul (x : ℝ) (k : ℕ) : phase ((k : ℝ) * x) = phase x ^ k := by
  unfold phase
  rw [Complex.ofReal_mul, mul_assoc, Complex.ofReal_natCast, Complex.exp_nat_mul]

lemma phase_sub (x y : ℝ) : phase (x - y) = phase x * star (phase y) := by
  unfold phase
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  have h : Complex.exp ((y : ℂ) * Complex.I) *
      star (Complex.exp ((y : ℂ) * Complex.I)) = 1 := by
    change Complex.exp ((y : ℂ) * Complex.I) *
      (starRingEnd ℂ) (Complex.exp ((y : ℂ) * Complex.I)) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have h_inv : star (Complex.exp ((y : ℂ) * Complex.I)) =
      (Complex.exp ((y : ℂ) * Complex.I))⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  rw [div_eq_mul_inv, h_inv]

lemma abs_le_norm_phase_sub_one {x : ℝ} (hx : |x| ≤ 1) :
    |x| ≤ 2 * ‖phase x - 1‖ := by
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsin : 2 / Real.pi * |x| ≤ Real.sin |x| :=
    Real.mul_le_sin (abs_nonneg _) (by linarith [Real.pi_gt_three])
  have hsn : |Real.sin x| = Real.sin |x| := by
    have hnonneg : 0 ≤ Real.sin |x| := (mul_nonneg (by positivity) (abs_nonneg _)).trans hsin
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h] at hnonneg ⊢
      exact abs_of_nonneg hnonneg
    · rw [abs_of_nonpos h, Real.sin_neg] at hnonneg ⊢
      exact abs_of_nonpos (by linarith)
  have him := Complex.abs_im_le_norm (phase x - 1)
  rw [Complex.sub_im, Complex.one_im, sub_zero, phase, Complex.exp_ofReal_mul_I_im, hsn] at him
  change Real.sin |x| ≤ ‖phase x - 1‖ at him
  have hπ : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hh : (1 / 2 : ℝ) ≤ 2 / Real.pi := (le_div_iff₀ hp).mpr (by linarith)
  have := (mul_le_mul_of_nonneg_right hh (abs_nonneg x)).trans (hsin.trans him)
  linarith

lemma norm_sum_linear {x : ℝ} (y : ℝ) (n : ℕ) (hx : 0 < |x|) (hx' : |x| ≤ 1) :
    ‖∑ j ∈ range n, phase (x * j + y)‖ ≤ 4 / |x| := by
  have hg : ‖∑ j ∈ range n, phase x ^ j‖ * ‖phase x - 1‖ ≤ 2 := by
    rw [← norm_mul, geom_sum_mul]
    exact (norm_sub_le _ _).trans (by norm_num [norm_pow])
  have h := mul_le_mul_of_nonneg_left (abs_le_norm_phase_sub_one hx')
    (norm_nonneg (∑ j ∈ range n, phase x ^ j))
  have hb : ‖∑ j ∈ range n, phase x ^ j‖ ≤ 4 / |x| :=
    (le_div_iff₀ hx).mpr (by nlinarith only [h, hg])
  simp_rw [phase_add, mul_comm x, phase_nat_mul]
  rw [← sum_mul, norm_mul, norm_phase, mul_one]
  exact hb

lemma norm_range_le (z : ℕ → ℂ) (hz : ∀ j, ‖z j‖ = 1) (n : ℕ) :
    ‖∑ j ∈ range n, z j‖ ≤ n :=
  (norm_sum_le _ _).trans_eq (by simp [hz])

lemma shift_sum (z : ℕ → ℂ) (hz : ∀ j, ‖z j‖ = 1) (n r : ℕ) :
    ‖(∑ j ∈ range n, z j) - ∑ j ∈ range n, z (j + r)‖ ≤ 2 * r := by
  have h := sum_range_add z n r
  rw [Nat.add_comm n r, sum_range_add z r n] at h
  have he : (∑ j ∈ range n, z j) - ∑ j ∈ range n, z (j + r) =
      (∑ j ∈ range r, z j) - ∑ j ∈ range r, z (n + j) := by
    simp_rw [Nat.add_comm _ r]
    linear_combination -h
  rw [he]
  exact (norm_sub_le _ _).trans (by
    linarith [norm_range_le z hz r, norm_range_le (fun j => z (n + j)) (fun j => hz _) r])

lemma square_sum_bound (w : ℕ → ℂ) (n : ℕ) :
    ‖∑ j ∈ range n, w j‖ ^ 2 ≤ n * ∑ j ∈ range n, ‖w j‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
  simpa [mul_comm] using sum_mul_sq_le_sq_mul_sq (range n) (fun j => ‖w j‖) (fun _ => (1 : ℝ))

lemma spaced_average (z : ℕ → ℂ) (hz : ∀ j, ‖z j‖ = 1) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (q : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hc : ∀ r ∈ range m, ∀ s ∈ range m, r ≠ s →
      ‖∑ j ∈ range n, z (j + r * q) * star (z (j + s * q))‖ ≤ n * E) :
    ‖∑ j ∈ range n, z j‖ / n ≤ 2 * m * q / n + Real.sqrt (1 / m + E) := by
  classical
  let S : ℂ := ∑ j ∈ range n, z j
  let w : ℕ → ℂ := fun j => ∑ r ∈ range m, z (j + r * q)
  let W : ℂ := ∑ j ∈ range n, w j
  have hnm : 0 < (n : ℝ) * m := by positivity
  have hshift : ‖(m : ℂ) * S - W‖ ≤ 2 * m * m * q := by
    have he : (m : ℂ) * S - W =
        ∑ r ∈ range m, (S - ∑ j ∈ range n, z (j + r * q)) := by
      rw [sum_sub_distrib]
      simp only [sum_const, card_range, nsmul_eq_mul]
      congr 1
      exact sum_comm
    rw [he]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ r ∈ range m, ‖S - ∑ j ∈ range n, z (j + r * q)‖ ≤ 2 * m * q := by
      intro r hr
      refine (shift_sum z hz n (r * q)).trans ?_
      push_cast
      have h : (r : ℝ) ≤ m := by exact_mod_cast (mem_range.mp hr).le
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2))
        (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    exact (sum_le_sum hb).trans (by simp only [sum_const, card_range, nsmul_eq_mul]; ring_nf; rfl)
  have hsplit :
      (∑ j ∈ range n, ((‖w j‖ ^ 2 : ℝ) : ℂ)) =
        ∑ r ∈ range m, ∑ s ∈ range m, ∑ j ∈ range n,
          z (j + r * q) * star (z (j + s * q)) := by
    simp only [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, w]
    simp only [map_sum, sum_mul]
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro r hr
    exact sum_comm
  have hb : ∀ r ∈ range m, ∀ s ∈ range m,
      ‖∑ j ∈ range n, z (j + r * q) * star (z (j + s * q))‖ ≤
        (if r = s then (n : ℝ) else 0) + n * E := by
    intro r hr s hs
    by_cases he : r = s
    · subst s
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, mul_nonneg (Nat.cast_nonneg n) hE]
    · simpa [he] using hc r hr s hs he
  have hsum : (∑ j ∈ range n, ‖w j‖ ^ 2) ≤ m * (n + m * (n * E)) := by
    have he : (∑ j ∈ range n, ‖w j‖ ^ 2) =
        ‖∑ j ∈ range n, ((‖w j‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      positivity
    rw [he, hsplit]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ r ∈ range m, ∑ s ∈ range m,
          ((if r = s then (n : ℝ) else 0) + n * E) :=
        sum_le_sum fun r hr => (norm_sum_le _ _).trans (sum_le_sum (hb r hr))
      _ = _ := by
        simp only [sum_add_distrib, sum_ite_eq, sum_const, card_range, nsmul_eq_mul]
        rw [sum_congr rfl (fun r hr => if_pos hr), sum_const, card_range, nsmul_eq_mul]
        ring
  have hw : ‖W‖ ≤ ((n : ℝ) * m) * Real.sqrt (1 / m + E) := by
    have hs : 0 ≤ 1 / (m : ℝ) + E := by positivity
    refine le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity) ?_
    calc
      ‖W‖ ^ 2 ≤ n * ∑ j ∈ range n, ‖w j‖ ^ 2 := square_sum_bound w n
      _ ≤ n * (m * (n + m * (n * E))) := by gcongr
      _ = ((n : ℝ) * m * Real.sqrt (1 / m + E)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hs]
        field_simp
  have ht : (m : ℝ) * ‖S‖ ≤ 2 * m * m * q + ((n : ℝ) * m) * Real.sqrt (1 / m + E) :=
    calc
      _ = ‖(m : ℂ) * S‖ := by simp
      _ = ‖((m : ℂ) * S - W) + W‖ := by rw [sub_add_cancel]
      _ ≤ ‖(m : ℂ) * S - W‖ + ‖W‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hshift hw
  change ‖S‖ / n ≤ _
  calc
    ‖S‖ / n = ((m : ℝ) * ‖S‖) / ((n : ℝ) * m) := by field_simp
    _ ≤ (2 * m * m * q + ((n : ℝ) * m) * Real.sqrt (1 / m + E)) / ((n : ℝ) * m) :=
      div_le_div_of_nonneg_right ht hnm.le
    _ = _ := by field_simp

lemma norm_average_quadratic {A : ℝ} (B C : ℝ) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hA : A ≠ 0)
    (hsmall : 2 * m * Real.sqrt |A| ≤ 1) :
    ‖∑ j ∈ range n, phase (A * (j : ℝ) ^ 2 + B * j + C)‖ / n ≤
      2 * m / (n * Real.sqrt |A|) +
        Real.sqrt (1 / m + 4 / (n * Real.sqrt |A|)) := by
  let a := Real.sqrt |A|
  have ha : 0 < a := Real.sqrt_pos_of_pos (abs_pos.mpr hA)
  have ha2 : a ^ 2 = |A| := Real.sq_sqrt (abs_nonneg A)
  change 2 * (m : ℝ) * a ≤ 1 at hsmall
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hale : a ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ 2 * m by linarith only [hm']) ha.le
    linarith only [this, hsmall]
  let q := ⌊1 / a⌋₊
  have hqu : (q : ℝ) * a ≤ 1 :=
    (le_div_iff₀ ha).mp (Nat.floor_le (by positivity))
  have hql : 1 / 2 ≤ (q : ℝ) * a := by
    have h := (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one (1 / a))
    linarith only [h, hale]
  let z : ℕ → ℂ := fun j => phase (A * (j : ℝ) ^ 2 + B * j + C)
  have h := spaced_average z (fun _ => norm_phase _) hn hm q
    (show 0 ≤ 4 / ((n : ℝ) * a) by positivity)
    (E := 4 / ((n : ℝ) * a)) (by
      intro r hr s hs hne
      have hrd : (r : ℝ) ≤ m := by exact_mod_cast (mem_range.mp hr).le
      have hsd : (s : ℝ) ≤ m := by exact_mod_cast (mem_range.mp hs).le
      have hdu : |(r : ℝ) - s| ≤ m := by
        have hr0 : (0 : ℝ) ≤ r := by positivity
        have hs0 : (0 : ℝ) ≤ s := by positivity
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hdl : 1 ≤ |(r : ℝ) - s| := by
        rcases lt_or_gt_of_ne hne with h | h
        · have hh : (r : ℝ) + 1 ≤ s := by exact_mod_cast h
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hh : (s : ℝ) + 1 ≤ r := by exact_mod_cast h
          rw [abs_of_nonneg (by linarith)]
          linarith
      let D : ℝ := 2 * A * ((r : ℝ) - s) * q
      have hD : |D| = 2 * (a * (↑q * a)) * |(r : ℝ) - s| := by
        simp only [D, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
          abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q), ← ha2]
        ring
      have hDlo : a ≤ |D| := by
        rw [hD]
        calc a = 2 * (a * (1 / 2)) * 1 := by ring
          _ ≤ _ := by gcongr
      have hDhi : |D| ≤ 1 := by
        rw [hD]
        refine le_trans ?_ hsmall
        calc
          _ ≤ 2 * (a * 1) * m := by gcongr
          _ = _ := by ring
      let K : ℝ := A * (((r : ℝ) * q) ^ 2 - ((s : ℝ) * q) ^ 2) + B * ((r : ℝ) - s) * q
      have he : ∀ j : ℕ, z (j + r * q) * star (z (j + s * q)) = phase (D * j + K) := by
        intro j
        simp only [z, ← phase_sub, Nat.cast_add, Nat.cast_mul]
        congr 1
        dsimp [D, K]
        ring
      simp only [he]
      calc
        _ ≤ 4 / |D| := norm_sum_linear K n (ha.trans_le hDlo) hDhi
        _ ≤ 4 / a := by gcongr
        _ = (n : ℝ) * (4 / ((n : ℝ) * a)) := by field_simp)
  change ‖∑ j ∈ range n, z j‖ / n ≤ _
  apply h.trans
  refine add_le_add_left ?_ _
  have hn' : (0 : ℝ) < n := by positivity
  apply (le_div_iff₀ (mul_pos hn' ha)).mpr
  have he : 2 * (m : ℝ) * q / n * (n * a) = 2 * m * ((q : ℝ) * a) := by field_simp
  rw [he]
  exact mul_le_of_le_one_right (by positivity) hqu


open Filter Topology in
lemma quadratic_cancellation {ι : Type*} {l : Filter ι}
    (A B C : ι → ℝ) (n : ι → ℕ)
    (hA : Tendsto A l (𝓝 0))
    (hg : Tendsto (fun i => (n i : ℝ) * Real.sqrt |A i|) l atTop) :
    Tendsto (fun i =>
      (∑ j ∈ range (n i), phase (A i * (j : ℝ) ^ 2 + B i * j + C i)) / (n i : ℂ))
      l (𝓝 0) := by
  have ha : Tendsto (fun i => Real.sqrt |A i|) l (𝓝 0) := by simpa using hA.abs.sqrt
  have hnz : ∀ᶠ i in l, A i ≠ 0 ∧ 0 < n i := by
    filter_upwards [(tendsto_atTop.1 hg) 1] with i hi
    constructor
    · intro h
      norm_num [h] at hi
    · by_contra! h
      norm_num [Nat.eq_zero_of_le_zero h] at hi
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε ^ 2)
  have hm0 : 0 < m := by
    have h : (0 : ℝ) < m := (by positivity : (0 : ℝ) < 1 / ε ^ 2).trans hm
    exact_mod_cast h
  have hs : Real.sqrt (1 / (m : ℝ)) < ε := by
    apply (Real.sqrt_lt' hε).2
    have h : 0 < ε ^ 2 := by positivity
    have h' := (div_lt_iff₀ h).mp hm
    exact (div_lt_iff₀ (by positivity)).mpr (by simpa [mul_comm] using h')
  have hsmall : ∀ᶠ i in l, 2 * (m : ℝ) * Real.sqrt |A i| ≤ 1 := by
    have h : Tendsto (fun i => 2 * (m : ℝ) * Real.sqrt |A i|) l (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 2 * (m : ℝ))).mul ha
    exact (h.eventually_lt_const zero_lt_one).mono fun i hi => hi.le
  have ht : Tendsto (fun i =>
      2 * (m : ℝ) / ((n i : ℝ) * Real.sqrt |A i|) +
        Real.sqrt (1 / (m : ℝ) + 4 / ((n i : ℝ) * Real.sqrt |A i|))) l
      (𝓝 (Real.sqrt (1 / (m : ℝ)))) := by
    simpa using (hg.const_div_atTop (2 * (m : ℝ))).add
      ((tendsto_const_nhds (x := 1 / (m : ℝ))).add (hg.const_div_atTop 4)).sqrt
  filter_upwards [hnz, hsmall, ht.eventually_lt_const hs] with i hi his hit
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _), norm_div, Complex.norm_natCast]
  exact (norm_average_quadratic (B i) (C i) hi.2 hm0 hi.1 his).trans_lt hit

end OMA.QuadraticCarry

namespace OMA.QuadraticCarry

open Filter Topology Finset MeasureTheory
open scoped ENNReal BigOperators
open UnitAddTorus

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def torusHaar (d : Type*) [Fintype d] : ProbabilityMeasure (UnitAddTorus d) :=
  ⟨volume, inferInstance⟩

lemma haar_fourier {d : Type*} [Fintype d] (k : d → ℤ) :
    (∫ x, mFourier k x ∂(torusHaar d : Measure (UnitAddTorus d))) =
      (if k = 0 then 1 else 0) := by
  classical
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := d))) 0 k
  simpa only [ContinuousMap.inner_toLp, mFourier_zero, ContinuousMap.one_apply,
    map_one, mul_one, eq_comm, torusHaar, ProbabilityMeasure.coe_mk] using h

lemma integral_sub_bound {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [CompactSpace Ω] (μ : ProbabilityMeasure Ω) (f g : C(Ω, ℂ))
    (hf : Integrable f (μ : Measure Ω)) (hg : Integrable g (μ : Measure Ω)) :
    dist (∫ x, f x ∂(μ : Measure Ω)) (∫ x, g x ∂(μ : Measure Ω)) ≤ dist f g := by
  rw [dist_eq_norm, ← integral_sub hf hg, dist_eq_norm]
  have h : ∀ᵐ x ∂(μ : Measure Ω), ‖f x - g x‖ ≤ ‖f - g‖ :=
    Filter.Eventually.of_forall fun x => (f - g).norm_coe_le_norm x
  simpa using norm_integral_le_of_norm_le_const h

lemma weyl {d ι : Type*} [Fintype d] {l : Filter ι}
    (μ : ι → ProbabilityMeasure (UnitAddTorus d))
    (h : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (fun i => ∫ x, mFourier k x ∂(μ i : Measure (UnitAddTorus d))) l (𝓝 0)) :
    Tendsto μ l (𝓝 (torusHaar d)) := by
  classical
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  have hint : ∀ (f : C(UnitAddTorus d, ℂ)) (ν : ProbabilityMeasure (UnitAddTorus d)),
      Integrable f (ν : Measure (UnitAddTorus d)) := by
    intro f ν
    exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : ∀ (f : C(UnitAddTorus d, ℂ)),
      f ∈ Submodule.span ℂ (Set.range (mFourier (d := d))) →
      Tendsto (fun i => ∫ x, f x ∂(μ i : Measure (UnitAddTorus d))) l
        (𝓝 (∫ x, f x ∂(torusHaar d : Measure (UnitAddTorus d)))) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨k, rfl⟩ := hf
      by_cases hk : k = 0
      · simp [hk, mFourier_zero, integral_const, tendsto_const_nhds]
      · simpa only [haar_fourier, if_neg hk] using h k hk
    | zero => simp [tendsto_const_nhds]
    | add f g hf hg ihf ihg =>
      simpa only [ContinuousMap.add_apply, integral_add, hint] using ihf.add ihg
    | smul c f hf ih =>
      simpa only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul] using
        (tendsto_const_nhds (x := c)).mul ih
  intro f
  let f' : C(UnitAddTorus d, ℂ) := f.toContinuousMap
  have hf : f' ∈ (Submodule.span ℂ (Set.range (mFourier (d := d)))).topologicalClosure := by
    simp [span_mFourier_closure_eq_top]
  change f' ∈ closure (Submodule.span ℂ (Set.range (mFourier (d := d))) :
    Set C(UnitAddTorus d, ℂ)) at hf
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.mp hf (ε / 3) (by positivity)
  have hh := Metric.tendsto_nhds.mp (hc g hg) (ε / 3) (by positivity)
  filter_upwards [hh] with i hi
  have h₁ := integral_sub_bound (μ i) f' g (hint _ _) (hint _ _)
  have h₂ := integral_sub_bound (torusHaar d) g f' (hint _ _) (hint _ _)
  rw [dist_comm g f'] at h₂
  let A₁ := ∫ x, f' x ∂(μ i : Measure (UnitAddTorus d))
  let A₂ := ∫ x, g x ∂(μ i : Measure (UnitAddTorus d))
  let A₃ := ∫ x, g x ∂(torusHaar d : Measure (UnitAddTorus d))
  let A₄ := ∫ x, f' x ∂(torusHaar d : Measure (UnitAddTorus d))
  have htri : dist A₁ A₄ ≤ dist A₁ A₂ + (dist A₂ A₃ + dist A₃ A₄) :=
    (dist_triangle A₁ A₂ A₄).trans (add_le_add_right (dist_triangle A₂ A₃ A₄) _)
  dsimp [A₁, A₂, A₃, A₄] at htri
  change dist (∫ x, f' x ∂(μ i : Measure (UnitAddTorus d)))
    (∫ x, f' x ∂(torusHaar d : Measure (UnitAddTorus d))) < ε
  linarith only [htri, h₁, h₂, hi, hd]

noncomputable def averageMeasure {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) (hN : 0 < N)
    (x : ℕ → Ω) : ProbabilityMeasure Ω :=
  ⟨(N : ℝ≥0∞)⁻¹ • ∑ i ∈ range N, Measure.dirac (x i), by
    constructor
    simp [Measure.smul_apply, Measure.finsetSum_apply, ENNReal.inv_mul_cancel, hN.ne']⟩

lemma averageMeasure_integral {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (N : ℕ) (hN : 0 < N) (x : ℕ → Ω) (f : Ω → ℂ) :
    (∫ t, f t ∂(averageMeasure N hN x : Measure Ω)) =
      (∑ i ∈ range N, f (x i)) / (N : ℂ) := by
  simp only [averageMeasure, ProbabilityMeasure.coe_mk, integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by simp)), Complex.real_smul]
  simp [integral_dirac, div_eq_inv_mul, Complex.ofReal_inv]

lemma averageMeasure_apply {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ) (hN : 0 < N) (x : ℕ → Ω) {S : Set Ω} [DecidablePred fun i => x i ∈ S]
    (hS : MeasurableSet S) :
    (averageMeasure N hN x : Measure Ω) S =
      (((range N).filter (fun i => x i ∈ S)).card : ℝ≥0∞) / N := by
  classical
  rw [averageMeasure, ProbabilityMeasure.coe_mk, Measure.smul_apply, Measure.finsetSum_apply _ _ _]
  rw [div_eq_mul_inv, mul_comm _ ((N : ℝ≥0∞)⁻¹)]
  change (N : ℝ≥0∞)⁻¹ * _ = _
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro i hi
  rw [Measure.dirac_apply' _ hS, Set.indicator_apply]
  split_ifs <;> norm_num

end OMA.QuadraticCarry

namespace OMA.QuadraticCarry

open Filter Topology Finset MeasureTheory Complex
open UnitAddTorus

lemma phase_sum {d : Type*} (s : Finset d) (f : d → ℝ) :
    phase (∑ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, phase_add, ih]

lemma fourier_phase {d : Type*} [Fintype d] (k : d → ℤ) (x : d → ℝ) :
    mFourier k (fun i => (x i : UnitAddCircle)) =
      phase (∑ i, 2 * Real.pi * k i * x i) := by
  rw [phase_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [fourier_coe_apply]
  unfold phase
  push_cast
  ring_nf

/-- Cancellation for vectors with coordinates at consecutive powers of a growing base.
The starting point and linear coefficients may vary arbitrarily. -/
lemma successive_power_cancellation {ι : Type*} {l : Filter ι} {d : ℕ}
    (p : ι → ℝ) (N : ι → ℕ) (a : ℝ) (ha : 0 < a) (B C : ι → ℝ)
    (hp : Tendsto p l atTop)
    (hN : Tendsto (fun i => (N i : ℝ) ^ 2 / p i ^ d) l atTop)
    (k : Fin d → ℤ) (hk : k ≠ 0) :
    Tendsto (fun i => (∑ j ∈ range (N i),
      mFourier k (fun r => (((a * (j : ℝ) ^ 2 + B i * j + C i) /
        p i ^ (r.val + 1) : ℝ) : UnitAddCircle))) / (N i : ℂ)) l (𝓝 0) := by
  classical
  let b : Fin d → ℝ := fun r => 2 * Real.pi * k r
  let A : ι → ℝ := fun i => ∑ r, a * b r / p i ^ (r.val + 1)
  let L : ι → ℝ := fun i => ∑ r, B i * b r / p i ^ (r.val + 1)
  let Q : ι → ℝ := fun i => ∑ r, C i * b r / p i ^ (r.val + 1)
  have hA : Tendsto A l (𝓝 0) := by
    have ht (r : Fin d) : Tendsto (fun i => a * b r / p i ^ (r.val + 1)) l (𝓝 0) :=
      ((tendsto_pow_atTop (by omega : (r.val + 1) ≠ 0)).comp hp).const_div_atTop _
    simpa [A] using tendsto_finsetSum Finset.univ (fun r _ => ht r)
  obtain ⟨r, hr⟩ := Function.ne_iff.mp hk
  let s := Finset.univ.filter (fun r => k r ≠ 0)
  have hn : s.Nonempty := ⟨r, mem_filter.mpr ⟨mem_univ _, hr⟩⟩
  let r₀ := s.min' hn
  have hr₀ : k r₀ ≠ 0 := (mem_filter.mp (min'_mem s hn)).2
  have hzero (j : Fin d) (hj : j < r₀) : b j = 0 := by
    suffices h : k j = 0 by simp [b, h]
    by_contra! h
    exact (not_lt_of_ge (min'_le s j (mem_filter.mpr ⟨mem_univ _, h⟩))) hj
  have hp1 : ∀ᶠ i in l, 1 ≤ p i := (tendsto_atTop.1 hp) 1
  have hscale : Tendsto (fun i => A i * p i ^ (r₀.val + 1)) l (𝓝 (a * b r₀)) := by
    have hs (j : Fin d) : Tendsto
        (fun i => (a * b j / p i ^ (j.val + 1)) * p i ^ (r₀.val + 1)) l
        (𝓝 (if j = r₀ then a * b r₀ else 0)) := by
      rcases lt_trichotomy j r₀ with hj | rfl | hj
      · simpa [hzero j hj, hj.ne] using tendsto_const_nhds (x := (0 : ℝ))
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hp1] with i hi
        simp only [if_true]
        field_simp
      · simp only [if_neg hj.ne']
        have hne : j.val - r₀.val ≠ 0 := by exact Nat.sub_ne_zero_of_lt hj
        refine (((tendsto_pow_atTop hne).comp hp).const_div_atTop (a * b j)).congr' ?_
        filter_upwards [hp1] with i hi
        have he : j.val + 1 = r₀.val + 1 + (j.val - r₀.val) := by
          have : r₀.val < j.val := hj
          omega
        simp only [he, pow_add, Function.comp_apply]
        field_simp
    simpa [A, sum_mul, sum_ite_eq'] using tendsto_finsetSum Finset.univ (fun j _ => hs j)
  let e : ℝ := |a * b r₀| / 2
  have he : 0 < e := by
    have hb : b r₀ ≠ 0 := by
      dsimp [b]
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (Int.cast_ne_zero.mpr hr₀)
    exact div_pos (abs_pos.mpr (mul_ne_zero ha.ne' hb)) (by norm_num)
  have hl : ∀ᶠ i in l, e ≤ |A i| * p i ^ (r₀.val + 1) := by
    have hf : e < |a * b r₀| := by dsimp [e] at *; linarith
    filter_upwards [hp1, hscale.abs.eventually_const_lt hf] with i hi hh
    simpa only [abs_mul, abs_of_nonneg (pow_nonneg (zero_le_one.trans hi) _)] using hh.le
  have hsq : Tendsto (fun i => ((N i : ℝ) * Real.sqrt |A i|) ^ 2) l atTop := by
    refine tendsto_atTop_mono' l ?_ (hN.const_mul_atTop he)
    filter_upwards [hp1, hl] with i hi hh
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
    have hyp : p i ^ (r₀.val + 1) ≤ p i ^ d := pow_le_pow_right₀ hi r₀.isLt
    have hp0 : 0 < p i ^ d := pow_pos (zero_lt_one.trans_le hi) _
    have hh' : e / p i ^ d ≤ |A i| := by
      refine (div_le_iff₀ hp0).mpr (hh.trans ?_)
      exact mul_le_mul_of_nonneg_left hyp (abs_nonneg _)
    calc
      e * ((N i : ℝ) ^ 2 / p i ^ d) = (N i : ℝ) ^ 2 * (e / p i ^ d) := by ring
      _ ≤ _ := by gcongr
  have hg : Tendsto (fun i => (N i : ℝ) * Real.sqrt |A i|) l atTop := by
    refine tendsto_atTop.2 fun u => ?_
    filter_upwards [(tendsto_atTop.1 hsq) (u ^ 2)] with i hi
    exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity) hi
  refine (quadratic_cancellation A L Q N hA hg).congr' ?_
  refine Filter.Eventually.of_forall fun i => ?_
  apply congrArg (fun z : ℂ => z / (N i : ℂ))
  apply sum_congr rfl
  intro j hj
  rw [fourier_phase]
  congr 1
  simp only [A, L, Q, sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  dsimp [b]
  ring

end OMA.QuadraticCarry

namespace OMA.QuadraticCarry
open Filter Topology Finset MeasureTheory Set
open scoped ENNReal
open UnitAddTorus

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def halfArc : Set UnitAddCircle :=
  (fun x : ℝ => (x : UnitAddCircle)) '' Set.Icc 0 (1 / 2)

lemma closed_halfArc : IsClosed halfArc :=
  (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed

lemma volume_halfArc : (volume : Measure UnitAddCircle) halfArc = 1 / 2 := by
  let a : ℝ := -(1 / 4)
  let q : ℝ → UnitAddCircle := fun x => x
  have mh := (AddCircle.measurePreserving_mk (1 : ℝ) a).map_eq
  have hv := AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))
  simp only [ENNReal.ofReal_one, one_smul] at hv
  rw [hv] at mh
  change Measure.map q (volume.restrict (Ioc a (a + 1))) = _ at mh
  change AddCircle.haarAddCircle halfArc = _
  have hq : Measurable q := (AddCircle.continuous_mk' 1).measurable
  rw [← mh, Measure.map_apply hq closed_halfArc.measurableSet,
    Measure.restrict_apply (hq closed_halfArc.measurableSet)]
  have he : (q ⁻¹' halfArc) ∩ Set.Ioc a (a + 1) = Set.Icc 0 (1 / 2) := by
    have hs : Icc 0 (1 / 2 : ℝ) ⊆ Ioc a (a + 1) := by
      intro x hx
      change 0 ≤ x ∧ x ≤ 1 / 2 at hx
      exact ⟨by dsimp [a]; linarith [hx.1], by dsimp [a]; linarith [hx.2]⟩
    ext x
    constructor
    · rintro ⟨⟨y, hy, hxy⟩, hx⟩
      have he := (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hs hy) hx).mp hxy
      rwa [← he]
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hs hx⟩
  rw [he, Real.volume_Icc]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

def halfBox (d : Type*) : Set (UnitAddTorus d) := {x | ∀ i, x i ∈ halfArc}

lemma closed_halfBox (d : Type*) : IsClosed (halfBox d) := by
  have he : halfBox d = ⋂ i : d, (fun x : UnitAddTorus d => x i) ⁻¹' halfArc := by
    ext x
    simp [halfBox]
  rw [he]
  exact isClosed_iInter fun i => closed_halfArc.preimage (continuous_apply i)

lemma volume_halfBox {d : Type*} [Fintype d] :
    (torusHaar d : Measure (UnitAddTorus d)) (halfBox d) = (1 / 2 : ℝ≥0∞) ^ Fintype.card d := by
  have he : halfBox d = Set.pi univ (fun _ => halfArc) := by
    ext x; simp [halfBox]
  rw [he]
  change (Measure.pi (fun _ : d => volume)) (Set.pi univ (fun _ => halfArc)) = _
  rw [Measure.pi_pi]
  simp [volume_halfArc]

lemma frac_mem_halfArc {n q : ℕ} (hq : 0 < q) (h : 2 * (n % q) < q) :
    (((n : ℝ) / q : ℝ) : UnitAddCircle) ∈ halfArc := by
  have hp : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨((n % q : ℕ) : ℝ) / q, ⟨by positivity, ?_⟩, ?_⟩
  · apply (div_le_iff₀ hp).mpr
    have h' : 2 * ((n % q : ℕ) : ℝ) < q := by exact_mod_cast h
    linarith
  · have he : (n : ℝ) / q = ((n / q : ℕ) : ℝ) + ((n % q : ℕ) : ℝ) / q := by
      field_simp
      exact_mod_cast (Nat.div_add_mod n q).symm
    have h0 : (((n / q : ℕ) : ℝ) : UnitAddCircle) = 0 := by
      rw [← mul_one (((n / q : ℕ) : ℝ)), ← nsmul_eq_mul, AddCircle.coe_nsmul,
        AddCircle.coe_period, nsmul_zero]
    rw [he, AddCircle.coe_add, h0, zero_add]

lemma halfBox_upper_density {d ι : Type*} [Fintype d] {l : Filter ι}
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (x : ι → ℕ → UnitAddTorus d)
    (h : Tendsto (fun i => averageMeasure (N i) (hN i) (x i)) l (𝓝 (torusHaar d)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ((by classical exact
      ((range (N i)).filter (fun j => x i j ∈ halfBox d)).card : ℕ) : ℝ) / N i <
      (1 / 2 : ℝ) ^ Fintype.card d + ε := by
  classical
  let μ := fun i => averageMeasure (N i) (hN i) (x i)
  have hv := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h
    (closed_halfBox d)
  rw [volume_halfBox] at hv
  have hbdd : l.IsBoundedUnder (· ≤ ·) (fun i => (μ i : Measure (UnitAddTorus d)) (halfBox d)) := by
    refine ⟨1, eventually_map.mpr (Filter.Eventually.of_forall fun i => ?_)⟩
    exact prob_le_one (μ := (μ i : Measure (UnitAddTorus d)))
  have hpow : (1 / 2 : ℝ≥0∞) ^ Fintype.card d ≠ ∞ := by finiteness
  have hlt : (1 / 2 : ℝ≥0∞) ^ Fintype.card d <
      (1 / 2 : ℝ≥0∞) ^ Fintype.card d + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hpow (by simpa using hε)
  filter_upwards [eventually_lt_of_limsup_lt (hv.trans_lt hlt) hbdd] with i hi
  have hcast := (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr hi
  rw [averageMeasure_apply _ _ _ (closed_halfBox d).measurableSet, ENNReal.toReal_div,
    ENNReal.toReal_add hpow ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le,
    ENNReal.toReal_pow, ENNReal.toReal_div] at hcast
  simpa using hcast

end OMA.QuadraticCarry

namespace OMA.QuadraticCarry
open Finset Nat

def family (t : ℕ) : ℕ := 6 * t ^ 2 + 11 * t + 3

def carries (n p : ℕ) : Finset ℕ :=
  (Ico 1 (Nat.log p (2 * n) + 1)).filter (fun i => p ^ i ≤ 2 * (n % p ^ i))

def passes (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ p ∈ ((n + 1) * (n + 2)).primeFactors,
    2 * ((n + 1) * (n + 2)).factorization p ≤ (carries n p).card

lemma H3_of_infinite_passes (h : {n : ℕ | passes n}.Infinite) :
    OMA.R_Erdos727_erdos_727_variants_k_2_R1.H3 := by
  apply h.mono
  intro n hn
  change passes n at hn
  refine ⟨hn.1, ?_⟩
  dsimp only
  intro p hp
  have hc := hn.2 p hp
  have hcard : (carries n p).card ≤ Nat.log p (2 * n) := by
    unfold carries
    refine (Finset.card_filter_le _ _).trans_eq ?_
    simp
  refine ⟨?_, hc⟩
  exact (Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos
    (hc.trans hcard)).trans (Nat.pow_log_le_self p (by have h := hn.1; omega))

lemma mem_carries {n p i : ℕ} (hp : p.Prime)
    (hi : 1 ≤ i) (hh : p ^ i ≤ 2 * (n % p ^ i)) : i ∈ carries n p := by
  have hpow : p ^ i ≤ 2 * n := hh.trans (Nat.mul_le_mul_left _ (Nat.mod_le _ _))
  have hil := Nat.le_log_of_pow_le hp.one_lt hpow
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hi, by omega⟩, hh⟩

/-- Carry interval criterion adapted from LordMike’s checked k = 1 proof. -/
lemma middle_carry (n P q : ℕ) (h₁ : 2 * (P * q) + P ≤ 2 * n)
    (h₂ : n < P * (q + 1)) : P ≤ 2 * (n % P) := by
  have hq : n / P = q := Nat.div_eq_of_lt_le
    (by have hm : q * P = P * q := Nat.mul_comm _ _; omega)
    (by simpa [Nat.mul_comm] using h₂)
  have h := Nat.div_add_mod n P
  rw [hq] at h
  omega

lemma prime_congr_six {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hp2 : p % 2 ≠ 0 := by
    intro h
    have he := (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have he := (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  rw [← Nat.mod_mod_of_dvd p (show 2 ∣ 6 by decide)] at hp2
  rw [← Nat.mod_mod_of_dvd p (show 3 ∣ 6 by decide)] at hp3
  omega

lemma square_residue {p a r s : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hm : (p * a) % 6 = r) (hr : r * r % 6 = s) : a ^ 2 % 6 = s := by
  calc
    a ^ 2 % 6 = (p * a) ^ 2 % 6 := by
      rw [mul_pow, Nat.mul_mod (p ^ 2), pow_two p, Nat.mul_mod p p]
      rcases prime_congr_six hp hp7 with h | h
      · simp [h]
      · norm_num [h, Nat.mod_mod]
    _ = s := by rw [pow_two, Nat.mul_mod (p * a), hm, hr]

lemma large_prime_second_carry {t p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hlarge : 10 * (6 * t + 8) ≤ p ^ 2)
    (hdiv : p ∣ 6 * t + 6 ∨ p ∣ 6 * t + 3 ∨ p ∣ 6 * t + 8) :
    2 ∈ carries (family t) p := by
  have h6 : 6 * family t + 12 = (6 * t + 5) * (6 * t + 6) := by unfold family; ring
  have h3 : 6 * family t + 6 = (6 * t + 3) * (6 * t + 8) := by unfold family; ring
  have hp2 : 49 ≤ p ^ 2 := Nat.pow_le_pow_left hp7 2
  refine mem_carries hp (by omega) ?_
  rcases hdiv with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨a, ha⟩
  · have ha0 : a ^ 2 % 6 = 0 :=
      square_residue hp hp7 (r := 0) (by rw [← ha]; omega) (by decide)
    have ha6 := Nat.div_add_mod (a ^ 2) 6
    have ha2 : 6 ≤ a ^ 2 := by
      rw [ha0, add_zero] at ha6
      have hapos : 0 < a := by
        by_contra! h
        simp [Nat.eq_zero_of_le_zero h] at ha
      have h : 0 < a ^ 2 := by positivity
      omega
    have hmain : 6 * family t + 12 + p * a = a ^ 2 * p ^ 2 := by
      calc
        _ = (6 * t + 6) * (6 * t + 6) := by rw [← ha, h6]; ring
        _ = _ := by rw [ha]; ring
    let k := a ^ 2 / 6 - 1
    have hak : a ^ 2 = 6 * (k + 1) := by dsimp [k]; omega
    have hbounds : 6 * family t + 12 + (6 * t + 6) =
        6 * (p ^ 2 * k) + 6 * p ^ 2 := by rw [ha, hmain, hak]; ring
    apply middle_carry (q := k)
    · omega
    · rw [Nat.mul_succ]
      omega
  · have ha3 : a ^ 2 % 6 = 3 :=
      square_residue hp hp7 (r := 3) (by rw [← ha]; omega) (by decide)
    let k := a ^ 2 / 6
    have hak : a ^ 2 = 6 * k + 3 := by
      have he := Nat.div_add_mod (a ^ 2) 6
      rw [ha3] at he
      exact he.symm
    have hmain : 6 * family t + 6 = a ^ 2 * p ^ 2 + 5 * (p * a) := by
      calc
        _ = (6 * t + 3) * ((6 * t + 3) + 5) := by rw [h3]
        _ = _ := by rw [ha]; ring
    have hbounds : 6 * family t + 6 =
        6 * (p ^ 2 * k) + 3 * p ^ 2 + 5 * (6 * t + 3) := by rw [ha, hmain, hak]; ring
    apply middle_carry (q := k)
    · omega
    · rw [Nat.mul_succ]
      omega
  · have ha4 : a ^ 2 % 6 = 4 :=
      square_residue hp hp7 (r := 2) (by rw [← ha]; omega) (by decide)
    let k := a ^ 2 / 6
    have hak : a ^ 2 = 6 * k + 4 := by
      have he := Nat.div_add_mod (a ^ 2) 6
      rw [ha4] at he
      exact he.symm
    have hmain : 6 * family t + 6 + 5 * (p * a) = a ^ 2 * p ^ 2 := by
      calc
        _ = (6 * t + 8) * (6 * t + 8) := by rw [← ha, h3]; ring
        _ = _ := by rw [ha]; ring
    have hbounds : 6 * family t + 6 + 5 * (6 * t + 8) =
        6 * (p ^ 2 * k) + 4 * p ^ 2 := by rw [ha, hmain, hak]; ring
    apply middle_carry (q := k)
    · omega
    · rw [Nat.mul_succ]
      omega

lemma passes_208 : passes 208 := by
  refine ⟨by decide, ?_⟩
  have hs : ((208 + 1) * (208 + 2) : ℕ).primeFactors = {2, 3, 5, 7, 11, 19} := by
    decide +kernel
  intro p hp
  rw [hs] at hp
  fin_cases hp <;> decide +kernel

end OMA.QuadraticCarry

namespace OMA.QuadraticCarry

open Finset Nat

def shiftProduct (n : ℕ) : ℕ := (n + 1) * (n + 2)

def offset : Fin 4 → ℕ := ![5, 6, 3, 8]

def branch (b : Fin 4) (t : ℕ) : ℕ := 6 * t + offset b

lemma offset_range (b : Fin 4) : 3 ≤ offset b ∧ offset b ≤ 8 := by
  fin_cases b <;> decide

lemma offset_injective : Function.Injective offset := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

lemma branch_pos (b : Fin 4) (t : ℕ) : 0 < branch b t := by
  have h := (offset_range b).1
  unfold branch
  omega

lemma product_branches (t : ℕ) :
    (∏ b : Fin 4, branch b t) = 36 * shiftProduct (family t) := by
  simp only [Fin.prod_univ_succ, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  change (6 * t + 5) * ((6 * t + 6) * ((6 * t + 3) * (6 * t + 8))) = _
  unfold shiftProduct family
  ring

lemma prime_not_dvd_6 {p : ℕ} (h7 : 7 ≤ p) : ¬p ∣ 6 := fun h =>
  (by omega : ¬p ≤ 6) (Nat.le_of_dvd (by decide) h)

lemma prime_not_dvd_36 {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : ¬p ∣ 36 := by
  change ¬ p ∣ 6 * 6
  rw [hp.dvd_mul]
  simp [prime_not_dvd_6 h7]

lemma unique_branch {p t : ℕ} (h7 : 7 ≤ p) {b c : Fin 4}
    (hb : p ∣ branch b t) (hc : p ∣ branch c t) : b = c := by
  rcases le_total (offset b) (offset c) with h | h
  · apply offset_injective
    have he : branch c t - branch b t = offset c - offset b := by
      unfold branch
      omega
    have hd : p ∣ offset c - offset b := he ▸ Nat.dvd_sub hc hb
    have hdiff := Nat.eq_zero_of_dvd_of_lt hd (by
      have h₁ := (offset_range b).1
      have h₂ := (offset_range c).2
      omega)
    omega
  · apply offset_injective
    have he : branch b t - branch c t = offset b - offset c := by
      unfold branch
      omega
    have hd : p ∣ offset b - offset c := he ▸ Nat.dvd_sub hb hc
    have hdiff := Nat.eq_zero_of_dvd_of_lt hd (by
      have h₁ := (offset_range c).1
      have h₂ := (offset_range b).2
      omega)
    omega

lemma exists_branch {p t : ℕ} (hp : p.Prime) (hd : p ∣ shiftProduct (family t)) :
    ∃ b : Fin 4, p ∣ branch b t := by
  have h : p ∣ ∏ b : Fin 4, branch b t := by
    rw [product_branches]
    exact hd.trans (Nat.dvd_mul_left _ _)
  rcases (hp.prime.dvd_finsetProd_iff _).mp h with ⟨b, _, hb⟩
  exact ⟨b, hb⟩

lemma val_eq_branch {p t : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) {b : Fin 4}
    (hb : p ∣ branch b t) :
    (shiftProduct (family t)).factorization p = (branch b t).factorization p := by
  have h := congrArg (fun x : ℕ => x.factorization p) (product_branches t)
  have h0 : shiftProduct (family t) ≠ 0 := by unfold shiftProduct; positivity
  rw [Nat.factorization_mul (by decide : 36 ≠ 0) h0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (prime_not_dvd_36 hp h7), zero_add] at h
  rw [← h, Nat.factorization_prod (fun c _ => (branch_pos c t).ne'), Finsupp.finsetSum_apply]
  rw [sum_eq_single b]
  · intro c hc hcb
    exact Nat.factorization_eq_zero_of_not_dvd fun hd => hcb (unique_branch h7 hd hb)
  · simp

lemma val_one_of_no_sq {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : p ∣ n) (h2 : ¬p ^ 2 ∣ n) : n.factorization p = 1 := by
  have h₁ : 1 ≤ n.factorization p :=
    (hp.pow_dvd_iff_le_factorization hn).mp (by simpa using h)
  have h₂ : ¬2 ≤ n.factorization p := fun hc =>
    h2 ((hp.pow_dvd_iff_le_factorization hn).mpr hc)
  omega

lemma first_carry {p n : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (hd : p ∣ shiftProduct n) : 1 ∈ carries n p := by
  have aux (i : ℕ) (hi : 1 ≤ i ∧ i ≤ 2) (h : p ∣ n + i) : p ≤ 2 * (n % p) := by
    obtain ⟨k, hk⟩ := h
    have hk1 : 1 ≤ k := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero (by omega : k ≤ 0)] at hk
      omega
    have hk' : p * k = p * (k - 1) + p := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [Nat.mul_succ]
    have hk'' : k - 1 + 1 = k := by omega
    apply middle_carry (q := k - 1)
    · omega
    · rw [hk'']
      omega
  refine mem_carries hp (by decide) ?_
  rw [pow_one]
  rcases hp.dvd_mul.mp hd with h | h
  · exact aux 1 (by decide) h
  · exact aux 2 (by decide) h

lemma two_of_carry {p n i : ℕ} (h1 : 1 ∈ carries n p) (hi : 2 ≤ i)
    (h : i ∈ carries n p) : 2 ≤ (carries n p).card := by
  have hsub : ({1, i} : Finset ℕ) ⊆ carries n p := by
    intro j hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact h1
    · exact h
  have hne : 1 ≠ i := by omega
  simpa [hne] using card_le_card hsub

lemma family_modEq {q a b : ℕ} (h : a ≡ b [MOD q]) :
    family a ≡ family b [MOD q] := by
  unfold family
  exact (((h.pow 2).mul_left 6).add (h.mul_left 11)).add_right 3

lemma shiftProduct_modEq {q a b : ℕ} (h : a ≡ b [MOD q]) :
    shiftProduct a ≡ shiftProduct b [MOD q] := by
  unfold shiftProduct
  exact (h.add_right 1).mul (h.add_right 2)

def parameter (P u : ℕ) : ℕ := 5 + P.factorial * u

lemma parameter_modEq {P u q : ℕ} (hq : q ∣ P.factorial) :
    parameter P u ≡ 5 [MOD q] := by
  rw [parameter, Nat.add_modEq_left_iff]
  exact hq.trans (Nat.dvd_mul_right _ _)

lemma family5 : family 5 = 208 := by decide

lemma fixed_primes_safe {P u p : ℕ} (hP : 416 ≤ P) (hp : p.Prime) (hpP : p ≤ P)
    (hdiv : p ∣ shiftProduct (family (parameter P u))) :
    2 * (shiftProduct (family (parameter P u))).factorization p ≤
      (carries (family (parameter P u)) p).card := by
  let n := family (parameter P u)
  have mod_of_le (q : ℕ) (hq : 0 < q) (h : q ≤ P) : n ≡ 208 [MOD q] := by
    rw [← family5]
    exact family_modEq (parameter_modEq (Nat.dvd_factorial hq h))
  have hW := shiftProduct_modEq (mod_of_le p hp.pos hpP)
  have hdiv' : p ∣ shiftProduct 208 :=
    Nat.modEq_zero_iff_dvd.mp (hW.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdiv))
  have hpW : p ∈ (shiftProduct 208).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hdiv', by decide⟩
  have hs : (shiftProduct 208).primeFactors = {2, 3, 5, 7, 11, 19} := by decide +kernel
  have hpp : p ^ 2 ≤ 416 := by
    rw [hs] at hpW
    fin_cases hpW <;> decide
  have hsq : ¬p ^ 2 ∣ shiftProduct n := by
    intro h
    have hmod := shiftProduct_modEq (mod_of_le (p ^ 2) (pow_pos hp.pos _) (hpp.trans hP))
    have hd := Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h))
    rw [hs] at hpW
    fin_cases hpW <;> exact (by decide : ¬_ ∣ _) hd
  have hv : (shiftProduct n).factorization p = 1 :=
    val_one_of_no_sq hp (by unfold shiftProduct; positivity) hdiv hsq
  change 2 * (shiftProduct n).factorization p ≤ (carries n p).card
  rw [hv, mul_one]
  have hcar : carries 208 p ⊆ carries n p := by
    intro i hi
    obtain ⟨hpos, hrem⟩ := mem_filter.mp hi
    have hlim : p ^ i ≤ 416 := hrem.trans (Nat.mul_le_mul_left _ (Nat.mod_le _ _))
    have hmod : n % p ^ i = 208 % p ^ i :=
      mod_of_le (p ^ i) (pow_pos hp.pos _) (hlim.trans hP)
    exact mem_carries hp (mem_Ico.mp hpos).1 (hmod ▸ hrem)
  apply le_trans _ (card_le_card hcar)
  rw [hs] at hpW
  fin_cases hpW <;> decide +kernel

end OMA.QuadraticCarry

namespace OMA.QuadraticCarry

open Finset Nat

lemma branch_congr {P u v p k : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hP : P < p)
    (b : Fin 4) (hu : p ^ k ∣ branch b (parameter P u)) (hv : p ^ k ∣ branch b (parameter P v)) :
    u ≡ v [MOD p ^ k] := by
  have h6 : ¬p ∣ 6 * P.factorial := by
    rw [hp.dvd_mul, hp.dvd_factorial]
    exact not_or.mpr ⟨prime_not_dvd_6 h7, hP.not_ge⟩
  have hc := hp.coprime_pow_of_not_dvd (m := k) h6
  have he (w : ℕ) : branch b (parameter P w) = 6 * P.factorial * w + (30 + offset b) := by
    unfold branch parameter
    ring
  have h := (Nat.modEq_zero_iff_dvd.mpr hu).trans (Nat.modEq_zero_iff_dvd.mpr hv).symm
  rw [he, he] at h
  exact Nat.ModEq.cancel_left_of_coprime hc.symm (Nat.ModEq.add_right_cancel' _ h)

lemma card_mod_filter_le (N q r : ℕ) :
    ((range N).filter (fun u => u % q = r)).card ≤ N / q + 1 := by
  classical
  rw [← card_range (N / q + 1)]
  apply card_le_card_of_injOn (fun u => u / q)
  · intro u hu
    have hl := mem_range.mp (mem_filter.mp hu).1
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hl.le))
  · intro u hu v hv he
    have hr₁ := (mem_filter.mp hu).2
    have hr₂ := (mem_filter.mp hv).2
    have h₁ := Nat.div_add_mod u q
    have h₂ := Nat.div_add_mod v q
    change u / q = v / q at he
    rw [he, hr₁] at h₁
    rw [hr₂] at h₂
    exact h₁.symm.trans h₂

lemma branch_counts {P N p k : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hP : P < p) (b : Fin 4) :
    ((range N).filter (fun u => p ^ k ∣ branch b (parameter P u))).card ≤ N / (p ^ k) + 1 := by
  classical
  let s := (range N).filter (fun u => p ^ k ∣ branch b (parameter P u))
  change s.card ≤ _
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv⟩ := hs
    refine (card_le_card (t := (range N).filter (fun u => u % (p ^ k) = v % (p ^ k))) ?_).trans
      (card_mod_filter_le _ _ _)
    intro u hu
    obtain ⟨hN, hd⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨hN, branch_congr hp h7 hP b hd (mem_filter.mp hv).2⟩
  · simp [not_nonempty_iff_eq_empty.mp hs]

lemma derivative_unit {p t s : ℕ} (h7 : 7 ≤ p) {b : Fin 4}
    (ht : p ∣ branch b t) (hs : p ∣ branch b s) : ¬p ∣ 6 * (t + s) + 11 := by
  intro h
  have ha := Nat.dvd_add ht hs
  have he : branch b t + branch b s = 6 * (t + s) + 2 * offset b := by unfold branch; ring
  rw [he] at ha
  rcases le_total (2 * offset b) 11 with hl | hl
  · have hd := Nat.dvd_sub h ha
    have he : (6 * (t + s) + 11) - (6 * (t + s) + 2 * offset b) = 11 - 2 * offset b := by omega
    rw [he] at hd
    have hb := (offset_range b).1
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd := Nat.dvd_sub ha h
    have he : (6 * (t + s) + 2 * offset b) - (6 * (t + s) + 11) = 2 * offset b - 11 := by omega
    rw [he] at hd
    have hb := (offset_range b).2
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

lemma family_congr_on_branch {P p k u v : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hP : P < p)
    {b : Fin 4}
    (hu : p ∣ branch b (parameter P u)) (hv : p ∣ branch b (parameter P v))
    (hF : family (parameter P u) ≡ family (parameter P v) [MOD p ^ k]) :
    u ≡ v [MOD p ^ k] := by
  let c := P.factorial * (6 * (parameter P u + parameter P v) + 11)
  have hpc : ¬p ∣ c := by
    unfold c
    rw [hp.dvd_mul, hp.dvd_factorial]
    exact not_or.mpr ⟨hP.not_ge, derivative_unit h7 hu hv⟩
  have he : family (parameter P u) + c * v = family (parameter P v) + c * u := by
    unfold c family parameter
    ring
  have h := hF.add_right (c * v)
  rw [he] at h
  exact Nat.ModEq.cancel_left_of_coprime (hp.coprime_pow_of_not_dvd hpc).symm
    (Nat.ModEq.add_left_cancel' _ h)

noncomputable def cleanResidues (p r k : ℕ) : Finset ℕ := by
  classical
  exact (range (p ^ k)).filter (fun n => n % p = r ∧
    ∀ j ∈ Icc 2 k, 2 * (n % p ^ j) < p ^ j)

lemma mem_cleanResidues {p r k n : ℕ} :
    n ∈ cleanResidues p r k ↔ n < p ^ k ∧ n % p = r ∧
      ∀ j ∈ Icc 2 k, 2 * (n % p ^ j) < p ^ j := by
  classical
  simp [cleanResidues]

lemma card_cleanResidues (p r k : ℕ) (hp : 0 < p) :
    (cleanResidues p r (k + 1)).card ≤ ((p + 1) / 2) ^ k := by
  induction k with
  | zero =>
    simp only [zero_add, pow_zero]
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha', ha'', _⟩ := mem_cleanResidues.mp ha
    obtain ⟨hb', hb'', _⟩ := mem_cleanResidues.mp hb
    have hal : a < p := by simpa using ha'
    have hbl : b < p := by simpa using hb'
    rw [Nat.mod_eq_of_lt hal] at ha''
    rw [Nat.mod_eq_of_lt hbl] at hb''
    exact ha''.trans hb''.symm
  | succ k ih =>
    let q := p ^ (k + 1)
    let D := (p + 1) / 2
    rw [pow_succ]
    have h := card_le_card_of_injOn
      (s := cleanResidues p r (k + 2)) (t := (cleanResidues p r (k + 1)) ×ˢ range D)
      (fun n => (n % q, n / q)) (by
        intro n hn
        obtain ⟨hlt, hnr', hbits⟩ := mem_cleanResidues.mp hn
        have htop := hbits (k + 2) (mem_Icc.mpr ⟨by omega, by rfl⟩)
        rw [Nat.mod_eq_of_lt hlt, pow_succ] at htop
        obtain ⟨h₁, h₂⟩ := Nat.div_add_mod n q, Nat.mod_lt n (pow_pos hp _)
        have hdig : 2 * (n / q) < p := by
          by_contra! hh
          have hm := Nat.mul_le_mul_left q hh
          have he : q * (2 * (n / q)) = 2 * (q * (n / q)) := by ring
          rw [he] at hm
          change 2 * n < q * p at htop
          omega
        refine mem_product.mpr ⟨mem_cleanResidues.mpr ⟨h₂, ?_, ?_⟩,
          mem_range.mpr (by dsimp [D]; omega)⟩
        · rw [Nat.mod_mod_of_dvd _ (by simp [q])]
          exact hnr'
        · intro j hj
          have hj' := mem_Icc.mp hj
          rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow p hj'.2)]
          exact hbits j (mem_Icc.mpr ⟨hj'.1, by omega⟩))
      (by
        intro x _ y _ he
        have h₁ := congrArg Prod.fst he
        have h₂ := congrArg Prod.snd he
        simp at h₁ h₂
        have hx := Nat.div_add_mod x q
        have hy := Nat.div_add_mod y q
        rw [h₁, h₂] at hx
        exact hx.symm.trans hy)
    rw [card_product, card_range] at h
    exact h.trans (Nat.mul_le_mul_right _ ih)

def onlyFirst (n p : ℕ) : Prop := ∀ i ∈ carries n p, i ≤ 1

instance (n p : ℕ) : Decidable (onlyFirst n p) := by
  unfold onlyFirst
  infer_instance

def branchBad (P N p : ℕ) (b : Fin 4) : Finset ℕ :=
  (range N).filter (fun u => p ∣ branch b (parameter P u) ∧ onlyFirst (family (parameter P u)) p)

lemma small_branch_counts {P N p k : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hP : P < p) (b : Fin 4) :
    (branchBad P N p b).card ≤ ((p + 1) / 2) ^ k * (N / p ^ (k + 1) + 1) := by
  classical
  let q := p ^ (k + 1)
  by_cases hs : (branchBad P N p b).Nonempty
  · obtain ⟨v, hv⟩ := hs
    let r := family (parameter P v) % p
    have h := card_le_card_of_injOn
      (s := branchBad P N p b) (t := (cleanResidues p r (k + 1)) ×ˢ range (N / q + 1))
      (fun u => (family (parameter P u) % q, u / q)) (by
        intro u hu
        obtain ⟨hN, hd, hc⟩ := mem_filter.mp hu
        have hF : family (parameter P u) ≡ family (parameter P v) [MOD p] := by
          apply family_modEq
          have hcong := branch_congr (k := 1) hp h7 hP b (by simpa using hd)
            (by simpa using (mem_filter.mp hv).2.1)
          rw [pow_one] at hcong
          exact (hcong.mul_left _).add_left _
        refine mem_product.mpr ⟨mem_cleanResidues.mpr ⟨Nat.mod_lt _ (pow_pos hp.pos _), ?_, ?_⟩,
          mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp hN).le))⟩
        · rw [Nat.mod_mod_of_dvd _ (by simp [q])]
          exact hF
        · intro j hj
          have hj' := mem_Icc.mp hj
          rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow p hj'.2)]
          by_contra! hh
          exact (by omega : ¬j ≤ 1) (hc j (mem_carries hp (by omega) hh)))
      (by
        intro u hu v hv he
        have hmod : family (parameter P u) ≡ family (parameter P v) [MOD q] := congrArg Prod.fst he
        have hquot : u / q = v / q := congrArg Prod.snd he
        have hr := family_congr_on_branch hp h7 hP (mem_filter.mp hu).2.1
          (mem_filter.mp hv).2.1 hmod
        have hu' := Nat.div_add_mod u q
        have hv' := Nat.div_add_mod v q
        change u % q = v % q at hr
        rw [hr, hquot] at hu'
        exact hu'.symm.trans hv')
    rw [card_product, card_range] at h
    exact h.trans (Nat.mul_le_mul_right _ (card_cleanResidues p r k hp.pos))
  · simp [not_nonempty_iff_eq_empty.mp hs]

end OMA.QuadraticCarry


namespace OMA.QuadraticCarry

open Filter Topology Finset MeasureTheory UnitAddTorus

def windowBad (M d p N a : ℕ) : Finset ℕ :=
  (range N).filter (fun j => ∀ r : Fin d,
    2 * (family (a + M * p * j) % p ^ (r.val + 3)) < p ^ (r.val + 3))

/-- In progressions of step M p, carry failure at levels 3 through d+2
has upper density at most 2^(-d), uniformly as p and N²/p^d grow. -/
lemma window_bound (M d : ℕ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ p N a : ℕ, 0 < p → 0 < N → K ≤ p → K * p ^ d ≤ N ^ 2 →
      ((windowBad M d p N a).card : ℝ) / N < (1 / 2 : ℝ) ^ d + ε := by
  classical
  by_contra! h
  choose p N a hp hN hpK hNK hbad using h
  let x : ℕ → ℕ → UnitAddTorus (Fin d) := fun i j r =>
    (((family (a i + M * p i * j) : ℝ) / (p i : ℝ) ^ (r.val + 3) : ℝ) : UnitAddCircle)
  have hpTop : Tendsto (fun i => (p i : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun i => ?_) tendsto_natCast_atTop_atTop
    exact_mod_cast hpK i
  have hNTop : Tendsto (fun i => (N i : ℝ) ^ 2 / (p i : ℝ) ^ d) atTop atTop := by
    refine tendsto_atTop_mono (fun i => ?_) tendsto_natCast_atTop_atTop
    refine (le_div_iff₀ (by positivity [hp i])).mpr ?_
    exact_mod_cast hNK i
  have hweak : Tendsto (fun i => averageMeasure (N i) (hN i) (x i)) atTop
      (𝓝 (torusHaar (Fin d))) := by
    apply weyl
    intro k hk
    let B : ℕ → ℝ := fun i => (12 * (a i : ℝ) + 11) * M / p i
    let C : ℕ → ℝ := fun i => (family (a i) : ℝ) / (p i : ℝ) ^ 2
    refine (successive_power_cancellation (fun i => (p i : ℝ)) N
      (6 * (M : ℝ) ^ 2) (by positivity) B C hpTop hNTop k hk).congr' ?_
    refine Eventually.of_forall fun i => ?_
    change _ = ∫ y, mFourier k y ∂(averageMeasure (N i) (hN i) (x i) : Measure _)
    rw [averageMeasure_integral]
    apply congrArg (fun z : ℂ => z / (N i : ℂ))
    apply sum_congr rfl
    intro j hj
    congr 1
    ext r
    dsimp only [x, B, C]
    congr 1
    have he : r.val + 3 = r.val + 1 + 2 := by omega
    rw [he, pow_add]
    unfold family
    push_cast
    have hp0 : (p i : ℝ) ≠ 0 := by positivity [hp i]
    field_simp
    ring
  have hev := halfBox_upper_density N hN x hweak hε
  obtain ⟨i, hi⟩ := Eventually.exists hev
  have hsub : windowBad M d (p i) (N i) (a i) ⊆
      (range (N i)).filter (fun j => x i j ∈ halfBox (Fin d)) := by
    intro j hj
    obtain ⟨hj, hkeep⟩ := mem_filter.mp hj
    refine mem_filter.mpr ⟨hj, fun r => ?_⟩
    simpa [x, Nat.cast_pow] using frac_mem_halfArc (pow_pos (hp i) _) (hkeep r)
  have hcard : ((windowBad M d (p i) (N i) (a i)).card : ℝ) / N i ≤
      (((range (N i)).filter (fun j => x i j ∈ halfBox (Fin d))).card : ℝ) / N i :=
    div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub) (by positivity)
  exact (not_lt_of_ge (hbad i)) (hcard.trans_lt (by simpa using hi))

end OMA.QuadraticCarry


/- Elementary Mertens estimates adapted from the merged Erdős 1100 normal-order H4 proof
by Marcus Buffett, based on his Erdős 377 proof and first estimates by senamakel. -/
section
open scoped Classical

namespace OMA.QuadraticCarry.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring


end OMA.QuadraticCarry.Mertens
end

section
open Filter Finset Real Asymptotics
open scoped Topology BigOperators
open OMA.QuadraticCarry.Mertens
namespace OMA.QuadraticCarry.MertensSecond
noncomputable abbrev S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
lemma Cpos : 0 ≤ mertens1Const := by
  exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
lemma Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n+1)-mertensG m| =
        |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = _ := by ring
lemma logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
    log (log n)) atTop (𝓝 b) := by
  have hC : CauchySeq mertensG := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => (mertens1Const+1)/log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logTop
    obtain ⟨m,hm,he⟩ := ((eventually_ge_atTop 2).and (hlim.eventually_lt_const hε)).exists
    refine ⟨m,fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply (Gdiff m n hm hn).trans_lt
    have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hp : 0≤(mertens1Const+1)*(1/log n) := mul_nonneg (by linarith [Cpos]) (by positivity [log_pos hn'])
    rw [mul_sub,←div_eq_mul_one_div]
    linarith
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hC
  let R (n : ℕ) := ((∑ p ∈ Nat.primesLE n, log p / p)-log n)/log n
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun n : ℕ => mertens1Const/log n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop logTop)
    filter_upwards [logTop.eventually_gt_atTop 0] with n hn
    dsimp only [R]
    rw [Real.norm_eq_abs, abs_div,abs_of_pos hn]
    exact div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat n) hn.le
  refine ⟨b,?_⟩
  simpa [R,mertensG] using hb.add hR
end OMA.QuadraticCarry.MertensSecond
end

namespace OMA.QuadraticCarry

open Filter Topology Finset Real
open OMA.QuadraticCarry.Mertens

lemma real_mertens : ∃ b : ℝ,
    Tendsto (fun x : ℝ => OMA.QuadraticCarry.MertensSecond.S x - log (log x)) atTop (𝓝 b) := by
  obtain ⟨b, hb⟩ := OMA.QuadraticCarry.MertensSecond.natMertens
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hlog : Tendsto (fun x : ℝ => log (⌊x⌋₊ : ℝ)) atTop atTop := OMA.QuadraticCarry.MertensSecond.logTop.comp hfloor
  have hlog2 : Tendsto (fun x : ℝ => (log x - log (⌊x⌋₊ : ℝ)) / log (⌊x⌋₊ : ℝ))
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (hlog.const_div_atTop (log 2))
    · filter_upwards [eventually_ge_atTop (1 : ℝ), hlog.eventually_gt_atTop 0] with x hx ht
      exact div_nonneg (sub_nonneg.mpr (log_le_log_floor_add x hx).1) ht.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ), hlog.eventually_gt_atTop 0] with x hx ht
      exact div_le_div_of_nonneg_right (by linarith [(log_le_log_floor_add x hx).2]) ht.le
  have hdiff : Tendsto (fun x : ℝ => log (log x) - log (log (⌊x⌋₊ : ℝ))) atTop (𝓝 0) := by
    have hadd : Tendsto (fun x : ℝ => 1 + (log x - log (⌊x⌋₊ : ℝ)) / log (⌊x⌋₊ : ℝ))
        atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hlog2
    have hcont := (continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hadd
    have hcont' : Tendsto
        (fun x : ℝ => log (1 + (log x - log (⌊x⌋₊ : ℝ)) / log (⌊x⌋₊ : ℝ)))
        atTop (𝓝 0) := by simpa [Function.comp_def] using hcont
    refine hcont'.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ), hlog.eventually_gt_atTop 0] with x hx ht
    have he : 1 + (log x - log (⌊x⌋₊ : ℝ)) / log (⌊x⌋₊ : ℝ) =
        log x / log (⌊x⌋₊ : ℝ) := by field_simp; ring
    rw [he, log_div (log_pos hx).ne' ht.ne']
  refine ⟨b, ?_⟩
  have ht : Tendsto (fun x : ℝ =>
        (OMA.QuadraticCarry.MertensSecond.S x - log (log (⌊x⌋₊ : ℝ))) -
          (log (log x) - log (log (⌊x⌋₊ : ℝ)))) atTop (𝓝 (b - 0)) :=
    (hb.comp hfloor).sub hdiff
  rw [sub_zero] at ht
  refine ht.congr (fun x => ?_)
  ring

noncomputable def primeBand (N : ℕ) (α β : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊(N : ℝ) ^ β⌋₊ \ Nat.primesLE ⌊(N : ℝ) ^ α⌋₊

lemma mem_primeBand {N p : ℕ} {α β : ℝ} (hN : 0 < N) :
    p ∈ primeBand N α β ↔ p.Prime ∧ (N : ℝ) ^ α < p ∧ (p : ℝ) ≤ (N : ℝ) ^ β := by
  have hb : 0 ≤ (N : ℝ) ^ β := Real.rpow_nonneg (by positivity) _
  have ha : 0 ≤ (N : ℝ) ^ α := Real.rpow_nonneg (by positivity) _
  simp only [primeBand, Finset.mem_sdiff, Nat.mem_primesLE]
  rw [Nat.le_floor_iff hb, Nat.le_floor_iff ha]
  constructor
  · rintro ⟨⟨hb, hp⟩, hn⟩
    exact ⟨hp, lt_of_not_ge (fun h => hn ⟨h, hp⟩), hb⟩
  · rintro ⟨hp, ha, hb⟩
    exact ⟨⟨hb, hp⟩, fun hn => ha.not_ge hn.1⟩

lemma band_tendsto (α β : ℝ) (ha : 0 < α) (hab : α ≤ β) :
    Tendsto (fun N : ℕ => ∑ p ∈ primeBand N α β, (1 : ℝ) / p) atTop
      (𝓝 (log (β / α))) := by
  obtain ⟨b, hm⟩ := real_mertens
  have hb : 0 < β := ha.trans_le hab
  have hN (c : ℝ) (hc : 0 < c) : Tendsto (fun N : ℕ => (N : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have ht := (hm.comp (hN β hb)).sub (hm.comp (hN α ha))
  have ht' : Tendsto (fun N : ℕ =>
      ((OMA.QuadraticCarry.MertensSecond.S ((N : ℝ) ^ β) - log (log ((N : ℝ) ^ β))) -
        (OMA.QuadraticCarry.MertensSecond.S ((N : ℝ) ^ α) - log (log ((N : ℝ) ^ α))))) atTop (𝓝 0) := by
    simpa using ht
  have hadd := (tendsto_const_nhds (x := log (β / α))).add ht'
  rw [add_zero] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hf : Nat.primesLE ⌊(N : ℝ) ^ α⌋₊ ⊆ Nat.primesLE ⌊(N : ℝ) ^ β⌋₊ :=
    fun p hp => Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans
        (Nat.floor_mono (rpow_le_rpow_of_exponent_le hN1.le hab)), (Nat.mem_primesLE.mp hp).2⟩
  have hsum := Finset.sum_sdiff (f := fun p : ℕ => (1 : ℝ) / p) hf
  change log (β / α) + ((OMA.QuadraticCarry.MertensSecond.S ((N : ℝ) ^ β) - log (log ((N : ℝ) ^ β))) -
      (OMA.QuadraticCarry.MertensSecond.S ((N : ℝ) ^ α) - log (log ((N : ℝ) ^ α)))) = _
  rw [log_div hb.ne' ha.ne', log_rpow (by positivity), log_rpow (by positivity),
    log_mul hb.ne' (log_pos hN1).ne', log_mul ha.ne' (log_pos hN1).ne']
  change ∑ p ∈ primeBand N α β, (1 : ℝ) / p + OMA.QuadraticCarry.MertensSecond.S ((N : ℝ) ^ α) =
    OMA.QuadraticCarry.MertensSecond.S ((N : ℝ) ^ β) at hsum
  linarith only [hsum]

lemma logThree_lt : Real.log 3 < 11 / 10 := by
  have h := Real.exp_one_gt_d9
  have ht : (221 / 200 : ℝ) ≤ Real.exp (1 / 10) := by
    have he := Real.sum_le_exp_of_nonneg (x := (1 / 10 : ℝ)) (by norm_num) 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at he ⊢
    linarith
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, Real.exp_add]
  have hh := mul_lt_mul_of_pos_right h (by norm_num : (0 : ℝ) < 221 / 200)
  exact (by linarith : (3 : ℝ) < Real.exp 1 * (221 / 200)).trans_le
    (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le)

end OMA.QuadraticCarry


namespace OMA.QuadraticCarry

open Filter Topology Finset Real Nat

lemma windowLength_bounds (N q : ℕ) (hq : 0 < q) :
    (N : ℝ) / q < ((N / q + 1 : ℕ) : ℝ) ∧
      ((N / q + 1 : ℕ) : ℝ) ≤ (N : ℝ) / q + 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · apply (div_lt_iff₀ hq').2
    exact_mod_cast (show N < (N / q + 1) * q by
      rw [Nat.add_mul, one_mul, Nat.mul_comm (N / q) q]
      have h₁ := Nat.div_add_mod N q
      have h₂ := Nat.mod_lt N hq
      omega)
  · rw [Nat.cast_add, Nat.cast_one]
    apply add_le_add_left
    apply (le_div_iff₀ hq').2
    exact_mod_cast (show N / q * q ≤ N by
      rw [Nat.mul_comm]
      exact Nat.mul_div_le _ _)

lemma normalized_branch_count {P N p k : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hP : P < p)
    (hN : 0 < N) (b : Fin 4) :
    ((((range N).filter (fun u => p ^ k ∣ branch b (parameter P u))).card : ℕ) : ℝ) / N ≤
      1 / (p : ℝ) ^ k + 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := (windowLength_bounds N (p ^ k) (pow_pos hp.pos _)).2
  rw [Nat.cast_pow] at h
  apply (div_le_iff₀ hN').mpr
  calc
    _ ≤ (((N / p ^ k + 1 : ℕ) : ℝ)) := by exact_mod_cast branch_counts hp h7 hP b
    _ ≤ (N : ℝ) / (p : ℝ) ^ k + 1 := h
    _ = _ := by field_simp

lemma normalized_small_branch {P N p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hP : P < p)
    (hN : 0 < N) (hk : 1 ≤ p.log N) (b : Fin 4) :
    ((branchBad P N p b).card : ℝ) / N ≤ 2 / p * (2 / 3 : ℝ) ^ (p.log N - 1) := by
  let k := p.log N - 1
  have hk' : k + 1 = p.log N := by dsimp [k]; omega
  let q := p ^ (k + 1)
  have hq : 0 < q := pow_pos hp.pos _
  have hqN : q ≤ N := by dsimp [q]; rw [hk']; exact Nat.pow_log_le_self p hN.ne'
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hle : (1 : ℝ) ≤ (N : ℝ) / q := (le_div_iff₀ hq').mpr (by simpa using (show (q : ℝ) ≤ N by exact_mod_cast hqN))
  have hdiv : (((N / q + 1 : ℕ) : ℝ)) ≤ 2 * ((N : ℝ) / q) := by
    linarith [(windowLength_bounds N q hq).2]
  let D := ((p + 1) / 2 : ℕ)
  have hD : (D : ℝ) / p ≤ 2 / 3 := by
    apply (div_le_iff₀ hp').mpr
    have h' : (2 : ℝ) * (D : ℝ) ≤ (p : ℝ) + 1 := by
      exact_mod_cast (show 2 * D ≤ p + 1 from Nat.mul_div_le _ _)
    have h7' : (7 : ℝ) ≤ p := by exact_mod_cast h7
    linarith
  have hc : ((branchBad P N p b).card : ℝ) ≤ (D : ℝ) ^ k * ((N / q + 1 : ℕ) : ℝ) := by
    exact_mod_cast small_branch_counts (k := k) hp h7 hP b
  apply (div_le_iff₀ hN').mpr
  calc
    _ ≤ (D : ℝ) ^ k * (2 * ((N : ℝ) / q)) :=
      hc.trans (mul_le_mul_of_nonneg_left hdiv (by positivity))
    _ = (2 / (p : ℝ) * ((D : ℝ) / p) ^ k) * N := by
      simp only [q, pow_succ, Nat.cast_mul, Nat.cast_pow, div_pow]
      field_simp
    _ ≤ _ := by
      change _ ≤ (2 / (p : ℝ) * (2 / 3 : ℝ) ^ k) * N
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hD _) (by positivity)) hN'.le

lemma count_in_window {P N p d : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hP : P < p)
    (b : Fin 4) :
    ∃ a : ℕ, (branchBad P N p b).card ≤
      (windowBad P.factorial d p (N / p + 1) a).card := by
  classical
  by_cases hs : (branchBad P N p b).Nonempty
  · obtain ⟨v, hv⟩ := hs
    refine ⟨parameter P (v % p), ?_⟩
    apply card_le_card_of_injOn (fun u => u / p)
    · intro u hu
      obtain ⟨hN, hd, hc⟩ := mem_filter.mp hu
      have hr := branch_congr (k := 1) hp h7 hP b (by simpa using hd)
        (by simpa using (mem_filter.mp hv).2.1)
      rw [pow_one] at hr
      change u % p = v % p at hr
      have hparam : parameter P (v % p) + P.factorial * p * (u / p) = parameter P u := by
        unfold parameter
        rw [← hr]
        conv_rhs => rw [← Nat.div_add_mod u p]
        generalize u / p = U
        generalize u % p = R
        ring
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp hN).le)), ?_⟩
      intro r
      change 2 * (family (parameter P (v % p) + P.factorial * p * (u / p)) %
        p ^ (r.val + 3)) < p ^ (r.val + 3)
      rw [hparam]
      by_contra! he
      exact (by omega : ¬ r.val + 3 ≤ 1) (hc _ (mem_carries hp (by omega) he))
    · intro u hu v hv he
      change u / p = v / p at he
      have hr := branch_congr (k := 1) hp h7 hP b
        (by simpa using (mem_filter.mp hu).2.1) (by simpa using (mem_filter.mp hv).2.1)
      rw [pow_one] at hr
      change u % p = v % p at hr
      have h₁ := Nat.div_add_mod u p
      have h₂ := Nat.div_add_mod v p
      rw [he, hr] at h₁
      exact h₁.symm.trans h₂
  · exact ⟨0, by simp [not_nonempty_iff_eq_empty.mp hs]⟩

lemma branch_window_eventually (P d : ℕ) (α β ε : ℝ)
    (hα : 0 < α) (hβ : β < 2 / (d + 2)) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ primeBand N α β, ∀ b : Fin 4, 7 ≤ p → P < p →
      ((branchBad P N p b).card : ℝ) / N ≤
        ((1 / 2 : ℝ) ^ d + ε) * (1 / p + 1 / N) := by
  obtain ⟨K, hK⟩ := window_bound P.factorial d (Nat.factorial_pos _) ε hε
  have hd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hg : 0 < 2 - ((d : ℝ) + 2) * β := by
    have h := (lt_div_iff₀ hd).mp hβ
    linarith
  have hTop (z : ℝ) (hz : 0 < z) : Tendsto (fun N : ℕ => (N : ℝ) ^ z) atTop atTop :=
    (tendsto_rpow_atTop hz).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), (tendsto_atTop.1 (hTop α hα)) K,
    (tendsto_atTop.1 (hTop _ hg)) K] with N hN hbelow hgrow
  intro p hp b h7 hP
  obtain ⟨hpp, hplo, hphi⟩ := (mem_primeBand hN).mp hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hKp : K ≤ p := by exact_mod_cast hbelow.trans hplo.le
  let L := N / p + 1
  have hL : 0 < L := Nat.succ_pos _
  obtain ⟨hLlo, hLhi⟩ := windowLength_bounds N p hpp.pos
  have hR : (p : ℝ) ^ (d + 2 : ℕ) ≤ (N : ℝ) ^ (β * ((d : ℝ) + 2)) := by
    rw [show (d : ℝ) + 2 = ((d + 2 : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_mul_natCast (by positivity : 0 ≤ (N : ℝ)) β (d + 2)]
    exact pow_le_pow_left₀ hp'.le hphi _
  have hc : (K : ℝ) * (p : ℝ) ^ (d + 2 : ℕ) ≤ (N : ℝ) ^ 2 := by
    calc
      _ ≤ (N : ℝ) ^ (2 - ((d : ℝ) + 2) * β) * (N : ℝ) ^ (β * ((d : ℝ) + 2)) :=
        mul_le_mul hgrow hR (by positivity) (by positivity)
      _ = _ := by
        rw [← Real.rpow_add hN', show 2 - ((d : ℝ) + 2) * β + β * ((d : ℝ) + 2) = 2 by ring]
        norm_num
  have hKL : K * p ^ d ≤ L ^ 2 := by
    have h₁ : (N : ℝ) ≤ (L : ℝ) * (p : ℝ) := (div_lt_iff₀ hp').mp hLlo |>.le
    have h₂ := hc.trans (pow_le_pow_left₀ hN'.le h₁ 2)
    rw [pow_add, mul_pow, ← mul_assoc] at h₂
    have h₃ := le_of_mul_le_mul_right h₂ (show 0 < (p : ℝ) ^ 2 by positivity)
    exact_mod_cast h₃
  obtain ⟨a, ha⟩ := count_in_window (P := P) (N := N) (d := d) hpp h7 hP b
  have hv := hK p L a hpp.pos hL hKp hKL
  have hcard : ((branchBad P N p b).card : ℝ) ≤
      ((1 / 2 : ℝ) ^ d + ε) * (L : ℝ) := by
    exact (show ((branchBad P N p b).card : ℝ) ≤ (windowBad P.factorial d p L a).card
      by exact_mod_cast ha).trans ((div_lt_iff₀ (by positivity : (0 : ℝ) < L)).mp hv).le
  apply (div_le_iff₀ hN').mpr
  calc
    _ ≤ _ := hcard
    _ ≤ ((1 / 2 : ℝ) ^ d + ε) * ((N : ℝ) / p + 1) :=
      mul_le_mul_of_nonneg_left hLhi (by positivity)
    _ = _ := by field_simp

end OMA.QuadraticCarry



namespace OMA.QuadraticCarry

open Filter Topology Finset

lemma logarithmic_band_bound (s : Finset ℕ) (N k : ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ^ (k + 1) ≤ N ∧ N < p ^ (k + 2)) :
    ∑ p ∈ s, (1 : ℝ) / p ≤ 4 := by
  classical
  by_cases h : s.Nonempty
  · let q := s.min' h
    have hqs : q ∈ s := min'_mem _ _
    obtain ⟨hq, _, hqN⟩ := hs q hqs
    have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
    have hq2 : ∀ p ∈ s, p ≤ q ^ 2 := by
      intro p hp
      have hN := (hs p hp).2.1
      have hqN' : N < (q ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        exact hqN.trans_le (Nat.pow_le_pow_right hq.pos (by omega))
      by_contra! hbad
      exact (hN.trans_lt hqN').not_ge (Nat.pow_le_pow_left hbad.le _)
    have hsub : s ⊆ Nat.primesLE (q ^ 2) := fun p hp =>
      Nat.mem_primesLE.mpr ⟨hq2 p hp, (hs p hp).1⟩
    apply le_of_mul_le_mul_right _ hlog
    show (∑ p ∈ s, (1 : ℝ) / p) * Real.log (q : ℝ) ≤ 4 * Real.log (q : ℝ)
    rw [sum_mul]
    calc
      _ ≤ ∑ p ∈ s, Real.log (p : ℝ) / p := by
        apply sum_le_sum
        intro p hp
        have hqp : (q : ℝ) ≤ p := by exact_mod_cast min'_le s p hp
        have h := Real.log_le_log (show (0 : ℝ) < q by exact_mod_cast hq.pos) hqp
        rw [div_mul_eq_mul_div, one_mul]
        exact div_le_div_of_nonneg_right h (by positivity)
      _ ≤ ∑ p ∈ Nat.primesLE (q ^ 2), Real.log (p : ℝ) / p :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => div_nonneg
          (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)) (by positivity))
      _ ≤ Real.log ((q ^ 2 : ℕ) : ℝ) + Real.log 4 := OMA.QuadraticCarry.Mertens.sum_log_div_le_nat _
      _ ≤ _ := by
        rw [Nat.cast_pow, Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ q by exact_mod_cast hq.two_le)
        norm_num at ⊢
        linarith
  · simp [not_nonempty_iff_eq_empty.mp h]

lemma small_prime_weight_bound (s : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hs : ∀ p ∈ s, p.Prime ∧ 40 ≤ p.log N) :
    ∑ p ∈ s, (8 : ℝ) / p * (2 / 3 : ℝ) ^ (p.log N - 1) ≤ 1 / 200 := by
  classical
  let level : ℕ → ℕ := fun p => p.log N - 1
  let r : ℝ := 2 / 3
  have hmap : ∀ p ∈ s, level p ∈ Ico 39 (N + 1) := by
    intro p hp
    have hk := (hs p hp).2
    have hb := Nat.log_le_self p N
    exact mem_Ico.mpr ⟨by dsimp [level]; omega, by dsimp [level]; omega⟩
  have hfiber := sum_fiberwise_of_maps_to hmap
    (fun p => (8 : ℝ) / p * r ^ level p)
  change ∑ p ∈ s, (8 : ℝ) / p * r ^ level p ≤ _
  rw [← hfiber]
  calc
    _ ≤ ∑ k ∈ Ico 39 (N + 1), 32 * r ^ k := by
      apply sum_le_sum
      intro k hk
      let t := s.filter fun p => level p = k
      have ht : ∀ p ∈ t, p.Prime ∧ p ^ (k + 1) ≤ N ∧ N < p ^ (k + 2) := by
        intro p hp
        obtain ⟨hps, hpk⟩ := mem_filter.mp hp
        obtain ⟨hpp, hpl⟩ := hs p hps
        have h₁ : p.log N = k + 1 := by dsimp [level] at hpk; omega
        have h₂ : (p.log N).succ = k + 2 := by omega
        exact ⟨hpp, h₁ ▸ Nat.pow_log_le_self p hN.ne',
          h₂ ▸ Nat.lt_pow_succ_log_self hpp.one_lt N⟩
      have hmain := logarithmic_band_bound t N k ht
      change ∑ p ∈ t, (8 : ℝ) / p * r ^ level p ≤ _
      calc
        _ = ∑ p ∈ t, (8 : ℝ) * (1 / p) * r ^ k := by
          apply sum_congr rfl
          intro p hp
          rw [(mem_filter.mp hp).2]
          ring
        _ = 8 * ((∑ p ∈ t, (1 : ℝ) / p) * r ^ k) := by
          rw [sum_mul, mul_sum]
          apply sum_congr rfl
          intro p hp
          ring
        _ ≤ 32 * r ^ k := by
          calc
            _ ≤ 8 * (4 * r ^ k) := by gcongr
            _ = _ := by ring
    _ = 32 * ∑ k ∈ Ico 39 (N + 1), r ^ k := by rw [mul_sum]
    _ ≤ 32 * (r ^ 39 / (1 - r)) := by
      gcongr
      exact geom_sum_Ico_le_of_lt_one (by norm_num [r]) (by norm_num [r])
    _ ≤ _ := by norm_num [r]

lemma inverse_square_sum (s : Finset ℕ) (P X : ℕ) (hP : 0 < P)
    (hs : ∀ p ∈ s, P < p ∧ p ≤ X) :
    ∑ p ∈ s, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / P := by
  by_cases hX : P ≤ X
  · have htel (Y : ℕ) (hY : P ≤ Y) : ∑ p ∈ Ioc P Y,
        ((1 : ℝ) / ((p - 1 : ℕ) : ℝ) - 1 / p) = 1 / (P : ℝ) - 1 / Y := by
      induction Y, hY using Nat.le_induction with
      | base => simp
      | succ Y hY ih =>
        have hI : Ioc P (Y + 1) = insert (Y + 1) (Ioc P Y) := by
          ext p
          simp only [mem_Ioc, mem_insert]
          omega
        rw [hI, sum_insert (by simp [mem_Ioc]), ih]
        simp
    calc
      _ ≤ ∑ p ∈ Ioc P X, (1 : ℝ) / (p : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (fun p hp => mem_Ioc.mpr (hs p hp))
          (fun p hp _ => by positivity)
      _ ≤ ∑ p ∈ Ioc P X, ((1 : ℝ) / ((p - 1 : ℕ) : ℝ) - 1 / p) := by
        apply sum_le_sum
        intro p hp
        have hp₂ : 2 ≤ p := by have h := (mem_Ioc.mp hp).1; omega
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        have hpos : (0 : ℝ) < (p : ℝ) - 1 := by
          have hh : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
          linarith
        have hp0 : (0 : ℝ) < p := by positivity
        calc
          (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / ((p - 1) * p) := by
            apply one_div_le_one_div_of_le (by positivity)
            nlinarith
          _ = _ := by field_simp; ring
      _ = _ := htel X hX
      _ ≤ _ := sub_le_self _ (by positivity)
  · have he : s = ∅ := eq_empty_iff_forall_notMem.mpr (fun p hp => hX ((hs p hp).1.le.trans (hs p hp).2))
    rw [he, sum_empty]
    positivity

lemma prime_count_error (C : ℕ) (hC : 0 < C) :
    Tendsto (fun N : ℕ => ((Nat.primesLE (C * N)).card : ℝ) / N) atTop (𝓝 0) := by
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hCN : Tendsto (fun N : ℕ => (C : ℝ) * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hC'
  have hlog : Tendsto (fun N : ℕ => Real.log ((C : ℝ) * (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hCN
  have hθ := hCN.eventually (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one)
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _
    (hlog.const_div_atTop ((Real.log 4 + 1) * C))
  filter_upwards [hθ, eventually_gt_atTop (0 : ℕ)] with N hθ hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  change (Nat.primeCounting ⌊(C : ℝ) * (N : ℝ)⌋₊ : ℝ) ≤
    (Real.log 4 + 1) * ((C : ℝ) * (N : ℝ)) / Real.log ((C : ℝ) * (N : ℝ)) at hθ
  rw [← Nat.cast_mul, Nat.floor_natCast] at hθ
  rw [Nat.primesLE_card_eq_primeCounting]
  apply (div_le_iff₀ hN').mpr
  push_cast at hθ
  calc
    _ ≤ (Real.log 4 + 1) * ((C : ℝ) * (N : ℝ)) / Real.log ((C : ℝ) * N) := hθ
    _ = ((Real.log 4 + 1) * (C : ℝ) / Real.log ((C : ℝ) * N)) * N := by ring

end OMA.QuadraticCarry



namespace OMA.QuadraticCarry

open Filter Topology Finset

def branchBound (P : ℕ) := 6 * P.factorial + 38

lemma branch_le_bound {P N u : ℕ} (hu : u < N) (b : Fin 4) :
    branch b (parameter P u) ≤ branchBound P * N := by
  have hb := (offset_range b).2
  have hu' := Nat.mul_le_mul_left (6 * P.factorial) hu.le
  have hN : 1 ≤ N := by omega
  have h38 := Nat.mul_le_mul_left 38 hN
  simp only [branch, parameter, branchBound, Nat.mul_add, Nat.add_mul, ← Nat.mul_assoc] at *
  omega

def eligible (P N : ℕ) : Finset ℕ :=
  (Nat.primesLE (branchBound P * N)).filter (fun p => P < p)

lemma eligible_info {P N p : ℕ} (hp : p ∈ eligible P N) :
    p.Prime ∧ P < p ∧ p ≤ branchBound P * N := by
  obtain ⟨hp, hf⟩ := mem_filter.mp hp
  obtain ⟨hN, hprime⟩ := Nat.mem_primesLE.mp hp
  exact ⟨hprime, hf, hN⟩

def overBranches (S : Finset ℕ) (B : Finset (Fin 4)) (f : ℕ → Fin 4 → Finset ℕ) : Finset ℕ :=
  S.biUnion (fun p => B.biUnion (f p))

lemma overBranches_bound {S : Finset ℕ} {B : Finset (Fin 4)} {f : ℕ → Fin 4 → Finset ℕ}
    {N : ℕ} (hN : 0 < N) (w : ℕ → ℝ)
    (h : ∀ p ∈ S, ∀ b ∈ B, ((f p b).card : ℝ) / N ≤ w p) :
    ((overBranches S B f).card : ℝ) / N ≤ (B.card : ℝ) * ∑ p ∈ S, w p := by
  have hcard : (overBranches S B f).card ≤ ∑ p ∈ S, ∑ b ∈ B, (f p b).card :=
    card_biUnion_le.trans (sum_le_sum fun p _ => card_biUnion_le)
  calc
    _ ≤ (∑ p ∈ S, ∑ b ∈ B, ((f p b).card : ℝ)) / N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = ∑ p ∈ S, ∑ b ∈ B, (((f p b).card : ℝ) / N) := by
      simp only [sum_div]
    _ ≤ ∑ p ∈ S, ∑ b ∈ B, w p :=
      sum_le_sum fun p hp => sum_le_sum (h p hp)
    _ = _ := by simp [mul_sum]

def divisible (P N p k : ℕ) (b : Fin 4) : Finset ℕ :=
  (range N).filter (fun u => p ^ k ∣ branch b (parameter P u))

lemma bad_subset_divisible (P N p : ℕ) (b : Fin 4) :
    branchBad P N p b ⊆ divisible P N p 1 b := by
  intro u hu
  obtain ⟨hN, hd, _⟩ := mem_filter.mp hu
  exact mem_filter.mpr ⟨hN, by simpa using hd⟩

noncomputable def primeDensityError (P N : ℕ) : ℝ :=
  (Nat.primesLE (branchBound P * N)).card / (N : ℝ)

noncomputable def bandMass (N : ℕ) (α β : ℝ) : ℝ :=
  ∑ p ∈ primeBand N α β, (1 : ℝ) / p

noncomputable def cell (P N : ℕ) (α β : ℝ) : Finset ℕ :=
  eligible P N ∩ primeBand N α β

lemma cell_bound {P N : ℕ} {α β a : ℝ} {B : Finset (Fin 4)}
    {f : ℕ → Fin 4 → Finset ℕ} (hN : 0 < N) (ha : 0 ≤ a)
    (h : ∀ p ∈ cell P N α β, ∀ b ∈ B, ((f p b).card : ℝ) / N ≤ a * (1 / p + 1 / N)) :
    ((overBranches (cell P N α β) B f).card : ℝ) / N ≤
      (B.card : ℝ) * (a * (bandMass N α β + primeDensityError P N)) := by
  refine (overBranches_bound hN _ h).trans ?_
  simp only [← mul_sum, sum_add_distrib]
  gcongr
  · exact sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_inter.mp hp).2)
      (fun p hp _ => by positivity)
  · simp only [sum_const, nsmul_eq_mul, primeDensityError]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by
      exact_mod_cast card_le_card (fun p hp => (mem_filter.mp (mem_inter.mp hp).1).1)) (by positivity)

abbrev allBranches : Finset (Fin 4) := univ
abbrev firstBranch : Finset (Fin 4) := {0}

def squareBad (P N : ℕ) : Finset ℕ :=
  overBranches (eligible P N) allBranches (fun p => divisible P N p 2)

def smallBad (P N : ℕ) : Finset ℕ :=
  overBranches ((eligible P N).filter (fun p => 40 ≤ p.log N)) allBranches (branchBad P N)

lemma square_bad_bound {P N : ℕ} (hP : 416 ≤ P) (hN : 0 < N) :
    ((squareBad P N).card : ℝ) / N ≤ 4 / P + 4 * primeDensityError P N := by
  unfold squareBad
  refine (overBranches_bound hN (fun p => 1 / (p : ℝ) ^ 2 + 1 / N) ?_).trans ?_
  · intro p hp b hb
    obtain ⟨hpp, hpP, _⟩ := eligible_info hp
    exact normalized_branch_count hpp (by omega) hpP hN b
  · simp only [Fintype.card_fin, card_univ, Nat.cast_ofNat, sum_add_distrib]
    rw [mul_add]
    apply add_le_add
    · rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [one_div] using inverse_square_sum (eligible P N) P (branchBound P * N)
        (by omega) (fun p hp => (eligible_info hp).2)
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simp only [sum_const, nsmul_eq_mul, primeDensityError, mul_one_div]
      exact div_le_div_of_nonneg_right (by
        exact_mod_cast card_filter_le _ _) (by positivity)

lemma small_bad_bound {P N : ℕ} (hP : 416 ≤ P) (hN : 0 < N) :
    ((smallBad P N).card : ℝ) / N ≤ 1 / 200 := by
  unfold smallBad
  refine (overBranches_bound hN (fun p => 2 / (p : ℝ) * (2 / 3 : ℝ) ^ (p.log N - 1)) ?_).trans ?_
  · intro p hp b hb
    obtain ⟨hp, hf⟩ := mem_filter.mp hp
    obtain ⟨hpp, hpP, _⟩ := eligible_info hp
    exact normalized_small_branch hpp (by omega) hpP hN (by omega) b
  · simp only [card_univ, Fintype.card_fin, Nat.cast_ofNat, mul_sum]
    exact (sum_congr rfl fun p _ => by ring).le.trans
      (small_prime_weight_bound _ N hN fun p hp =>
        ⟨(eligible_info (mem_filter.mp hp).1).1, (mem_filter.mp hp).2⟩)

noncomputable def mediumExp (η : ℝ) (j : ℕ) : ℝ := 2 / j - η

def mediumIndices : Finset ℕ := Icc 4 80

noncomputable def bandBad (P N : ℕ) (α β : ℝ) (B : Finset (Fin 4)) : Finset ℕ :=
  overBranches (cell P N α β) B (branchBad P N)

noncomputable def mediumBad (P N : ℕ) (η : ℝ) : Finset ℕ :=
  mediumIndices.biUnion (fun j => bandBad P N (mediumExp η (j + 1)) (mediumExp η j) allBranches)

noncomputable def transitionBad (P N : ℕ) (η : ℝ) : Finset ℕ :=
  bandBad P N (1 / 2 - η) (1 / 2 + η) allBranches

noncomputable def upperMiddleBad (P N : ℕ) (η : ℝ) : Finset ℕ :=
  bandBad P N (1 / 2 + η) (2 / 3 - η) firstBranch

noncomputable def upperTailBad (P N : ℕ) (η : ℝ) : Finset ℕ :=
  bandBad P N (2 / 3 - η) (1 + η) firstBranch

lemma medium_exp_bounds {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 1000)
    {j : ℕ} (hj : j ∈ mediumIndices) :
    0 < mediumExp η (j + 1) ∧ mediumExp η (j + 1) ≤ mediumExp η j ∧
      mediumExp η j < 2 / ((j - 2 : ℕ) + 2 : ℝ) := by
  obtain ⟨hj₁, hj₂⟩ := mem_Icc.mp hj
  have hj0 : (0 : ℝ) < j := by positivity
  have hj81 : (j : ℝ) + 1 ≤ 81 := by exact_mod_cast (show j + 1 ≤ 81 by omega)
  have hlow : (2 : ℝ) / 81 ≤ 2 / ((j : ℝ) + 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hj81
  unfold mediumExp
  push_cast
  have hdec : (2 : ℝ) / ((j : ℝ) + 1) ≤ 2 / (j : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hj0 (by linarith)
  have hc : ((j - 2 : ℕ) : ℝ) + 2 = j := by
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
    ring
  rw [hc]
  exact ⟨by linarith, by linarith, by linarith⟩

noncomputable def mediumDensity (P N : ℕ) (η : ℝ) : ℝ :=
  ∑ j ∈ mediumIndices, 4 * (((1 / 2 : ℝ) ^ (j - 2) + η) *
    (bandMass N (mediumExp η (j + 1)) (mediumExp η j) + primeDensityError P N))

lemma band_bad_crude {P N : ℕ} (hP : 416 ≤ P) (hN : 0 < N)
    (α β : ℝ) (B : Finset (Fin 4)) :
    ((bandBad P N α β B).card : ℝ) / N ≤
      (B.card : ℝ) * (bandMass N α β + primeDensityError P N) := by
  have hb := cell_bound (α := α) (β := β) (B := B) (a := 1) hN zero_le_one
    (f := branchBad P N) (by
      intro p hp b hb
      have hpp := eligible_info (P := P) (N := N) (mem_inter.mp hp).1
      have hh := normalized_branch_count (N := N) (k := 1) hpp.1 (by omega) hpp.2.1 hN b
      have hsub := card_le_card (bad_subset_divisible P N p b)
      simpa using (div_le_div_of_nonneg_right (by exact_mod_cast hsub) (show (0 : ℝ) ≤ N by positivity)).trans hh)
  simpa [bandBad] using hb

lemma medium_bad_eventually (P : ℕ) (hP : 416 ≤ P) (η : ℝ) (hη : 0 < η) (hη' : η < 1 / 1000) :
    ∀ᶠ N : ℕ in atTop, ((mediumBad P N η).card : ℝ) / N ≤ mediumDensity P N η := by
  have hev : ∀ᶠ N : ℕ in atTop, ∀ j ∈ mediumIndices,
      ∀ p ∈ primeBand N (mediumExp η (j + 1)) (mediumExp η j), ∀ b : Fin 4, 7 ≤ p → P < p →
        ((branchBad P N p b).card : ℝ) / N ≤
          ((1 / 2 : ℝ) ^ (j - 2) + η) * (1 / p + 1 / N) := by
    rw [eventually_all_finset]
    intro j hj
    have hh := medium_exp_bounds hη hη' hj
    exact branch_window_eventually P (j - 2) _ _ η hh.1 hh.2.2 hη
  filter_upwards [hev, eventually_gt_atTop (0 : ℕ)] with N hN hn
  unfold mediumBad mediumDensity
  have hc : ((mediumIndices.biUnion fun j => bandBad P N (mediumExp η (j + 1))
      (mediumExp η j) allBranches).card : ℝ) ≤
      ∑ j ∈ mediumIndices, ((bandBad P N (mediumExp η (j + 1)) (mediumExp η j) allBranches).card : ℝ) := by
    exact_mod_cast card_biUnion_le
  refine (div_le_div_of_nonneg_right hc (show (0 : ℝ) ≤ N by positivity)).trans ?_
  rw [sum_div]
  apply sum_le_sum
  intro j hj
  have hb := cell_bound (α := mediumExp η (j + 1)) (β := mediumExp η j)
    (B := allBranches) (f := branchBad P N) (a := (1 / 2 : ℝ) ^ (j - 2) + η)
    hn (by positivity) (by
      intro p hp b hb
      obtain ⟨he, hb'⟩ := mem_inter.mp hp
      have hpP := (eligible_info he).2.1
      exact hN j hj p hb' b (by omega) hpP)
  simpa [bandBad] using hb

lemma upper_middle_eventually (P : ℕ) (hP : 416 ≤ P) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ((upperMiddleBad P N η).card : ℝ) / N ≤
      (1 / 2 + η) * (bandMass N (1 / 2 + η) (2 / 3 - η) + primeDensityError P N) := by
  have h := branch_window_eventually P 1 (1 / 2 + η) (2 / 3 - η) η
    (by linarith) (by norm_num; linarith) hη
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with N hN hn
  have hb := cell_bound (α := 1 / 2 + η) (β := 2 / 3 - η) (B := firstBranch)
    (f := branchBad P N) (a := 1 / 2 + η) hn (by positivity) (by
      intro p hp b hb
      obtain ⟨he, hb'⟩ := mem_inter.mp hp
      have hpP := (eligible_info he).2.1
      simpa using hN p hb' b (by omega) hpP)
  simpa [upperMiddleBad, bandBad] using hb

end OMA.QuadraticCarry



namespace OMA.QuadraticCarry

open Filter Topology Finset

noncomputable def budget (η : ℝ) : ℝ :=
  (∑ j ∈ mediumIndices, 4 * (((1 / 2 : ℝ) ^ (j - 2) + η) *
    Real.log (mediumExp η j / mediumExp η (j + 1)))) +
  4 * Real.log ((1 / 2 + η) / (1 / 2 - η)) +
  (1 / 2 + η) * Real.log ((2 / 3 - η) / (1 / 2 + η)) +
  Real.log ((1 + η) / (2 / 3 - η))

lemma logFiveFour_lt : Real.log (5 / 4) < 23 / 100 := by
  have h := Real.sum_le_exp_of_nonneg (x := (23 / 100 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  exact (Real.log_lt_iff_lt_exp (by norm_num)).2 (by linarith)

lemma medium_budget_zero :
    (∑ j ∈ mediumIndices, 4 * (((1 / 2 : ℝ) ^ (j - 2) + 0) *
      Real.log (mediumExp 0 j / mediumExp 0 (j + 1)))) < 43 / 100 := by
  have hI : mediumIndices = insert 4 (Icc 5 80) := by
    ext j
    simp only [mediumIndices, mem_Icc, mem_insert]
    omega
  rw [hI, sum_insert (by simp [mem_Icc])]
  have hfour : 4 * (((1 / 2 : ℝ) ^ (4 - 2 : ℕ) + 0) *
      Real.log (mediumExp 0 4 / mediumExp 0 (4 + 1))) = Real.log (5 / 4) := by
    norm_num [mediumExp]
    ring
  rw [hfour]
  have hrest : (∑ j ∈ Icc 5 80, 4 * (((1 / 2 : ℝ) ^ (j - 2) + 0) *
      Real.log (mediumExp 0 j / mediumExp 0 (j + 1)))) ≤ 1 / 5 := by
    have hgeo : (∑ j ∈ Icc 5 80, (1 / 2 : ℝ) ^ (j - 2)) ≤ 1 / 4 := by
      have he : (∑ j ∈ Icc 5 80, (1 / 2 : ℝ) ^ (j - 2)) = ∑ k ∈ Ico 3 79, (1 / 2 : ℝ) ^ k := by
        apply sum_bij (fun j _ => j - 2)
        · intro j hj
          have hh := mem_Icc.mp hj
          exact mem_Ico.mpr ⟨by omega, by omega⟩
        · intro x hx y hy he
          have hh := mem_Icc.mp hx
          have hh' := mem_Icc.mp hy
          omega
        · intro k hk
          have hh := mem_Ico.mp hk
          exact ⟨k + 2, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intros
          rfl
      rw [he]
      exact (geom_sum_Ico_le_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).trans_eq (by norm_num)
    calc
      _ ≤ ∑ j ∈ Icc 5 80, (4 / 5 : ℝ) * (1 / 2 : ℝ) ^ (j - 2) := by
        apply sum_le_sum
        intro j hj
        have hj5 : (5 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
        have hpos : (0 : ℝ) < j := by linarith
        have he : mediumExp 0 j / mediumExp 0 (j + 1) = ((j : ℝ) + 1) / j := by
          unfold mediumExp
          push_cast
          field_simp
          ring
        rw [he, add_zero]
        have hl := Real.log_le_sub_one_of_pos (show 0 < ((j : ℝ) + 1) / j by positivity)
        have hh : ((j : ℝ) + 1) / j - 1 = 1 / j := by
          field_simp
          ring
        rw [hh] at hl
        have hf : (1 : ℝ) / j ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hj5
        have hc := mul_le_mul_of_nonneg_left (hl.trans hf)
          (show 0 ≤ (1 / 2 : ℝ) ^ (j - 2) by positivity)
        linarith
      _ = (4 / 5 : ℝ) * ∑ j ∈ Icc 5 80, (1 / 2 : ℝ) ^ (j - 2) := by rw [mul_sum]
      _ ≤ _ := by linarith
  linarith [logFiveFour_lt]

lemma budget_zero : budget 0 < 49 / 50 := by
  have hup : (1 / 2 : ℝ) * Real.log (4 / 3) + Real.log (3 / 2) =
      1 / 2 * Real.log 3 := by
    have h := Real.log_mul (show (4 / 3 : ℝ) ≠ 0 by norm_num)
      (show (3 / 2 : ℝ) ^ 2 ≠ 0 by norm_num)
    rw [show (4 / 3 : ℝ) * (3 / 2) ^ 2 = 3 by norm_num, Real.log_pow] at h
    norm_num at h
    linarith
  unfold budget
  have h : (4 : ℝ) * Real.log ((1 / 2 + 0) / (1 / 2 - 0)) +
      (1 / 2 + 0) * Real.log ((2 / 3 - 0) / (1 / 2 + 0)) +
      Real.log ((1 + 0) / (2 / 3 - 0)) = 1 / 2 * Real.log 3 := by
    norm_num
    exact hup
  linarith [medium_budget_zero, logThree_lt]

lemma continuous_budget : ContinuousAt budget 0 := by
  have hm (j : ℕ) : Continuous (fun η : ℝ => mediumExp η j) := by
    unfold mediumExp
    fun_prop
  have hmedium : ContinuousAt
      (fun η : ℝ => ∑ j ∈ mediumIndices, 4 * (((1 / 2 : ℝ) ^ (j - 2) + η) *
        Real.log (mediumExp η j / mediumExp η (j + 1)))) 0 := by
    apply tendsto_finsetSum
    intro j hj
    have hj0 : 0 < j := by have hh := (mem_Icc.mp hj).1; omega
    have h₁ : mediumExp 0 j ≠ 0 := by unfold mediumExp; simp; positivity
    have h₂ : mediumExp 0 (j + 1) ≠ 0 := by unfold mediumExp; simp; positivity
    have hdiv : ContinuousAt (fun η => mediumExp η j / mediumExp η (j + 1)) 0 :=
      (hm j).continuousAt.div (hm (j + 1)).continuousAt h₂
    have hlog : ContinuousAt (fun η => Real.log (mediumExp η j / mediumExp η (j + 1))) 0 :=
      hdiv.log (div_ne_zero h₁ h₂)
    have hlin : ContinuousAt (fun η : ℝ => (1 / 2 : ℝ) ^ (j - 2) + η) 0 := by fun_prop
    exact (continuousAt_const.mul (hlin.mul hlog)).tendsto
  have hlog (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
      ContinuousAt (fun η => Real.log ((a + b * η) / (c + d * η))) 0 := by
    have h₁ : Continuous (fun η : ℝ => a + b * η) := by fun_prop
    have h₂ : Continuous (fun η : ℝ => c + d * η) := by fun_prop
    have hdiv : ContinuousAt (fun η : ℝ => (a + b * η) / (c + d * η)) 0 :=
      h₁.continuousAt.div h₂.continuousAt (by simpa using hc)
    have hne : (a + b * 0) / (c + d * 0) ≠ 0 := by simpa using div_ne_zero ha hc
    exact hdiv.log hne
  have h₁ : ContinuousAt (fun η => 4 * Real.log ((1 / 2 + η) / (1 / 2 - η))) 0 := by
    have h : ContinuousAt (fun η : ℝ => Real.log ((1 / 2 + η) / (1 / 2 - η))) 0 := by
      simpa [sub_eq_add_neg] using hlog (1/2) 1 (1/2) (-1) (by norm_num) (by norm_num)
    exact continuousAt_const.mul h
  have h₂ : ContinuousAt
      (fun η => (1 / 2 + η) * Real.log ((2 / 3 - η) / (1 / 2 + η))) 0 := by
    have h : ContinuousAt (fun η : ℝ => Real.log ((2 / 3 - η) / (1 / 2 + η))) 0 := by
      simpa [sub_eq_add_neg] using hlog (2/3) (-1) (1/2) 1 (by norm_num) (by norm_num)
    have hlin : ContinuousAt (fun η : ℝ => 1 / 2 + η) 0 := by fun_prop
    exact hlin.mul h
  have h₃ : ContinuousAt (fun η => Real.log ((1 + η) / (2 / 3 - η))) 0 := by
    simpa [sub_eq_add_neg] using hlog 1 1 (2/3) (-1) one_ne_zero (by norm_num)
  exact ((hmedium.add h₁).add h₂).add h₃

lemma choose_margin : ∃ η : ℝ, 0 < η ∧ η < 1 / 1000 ∧ budget η < 99 / 100 := by
  have hb : budget 0 < (99 / 100 : ℝ) := budget_zero.trans (by norm_num)
  have h := continuous_budget.tendsto.eventually_lt_const hb
  have h' := Metric.eventually_nhds_iff.mp h
  obtain ⟨δ, hδ, hδ'⟩ := h'
  let η := min (δ / 2) (1 / 2000)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  refine ⟨η, hη, (min_le_right _ _).trans_lt (by norm_num), hδ' ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hη]
  exact (min_le_left _ _).trans_lt (by linarith)

end OMA.QuadraticCarry

namespace OMA.QuadraticCarry

open Filter Topology Finset

noncomputable def excluded (P N : ℕ) (η : ℝ) : Finset ℕ :=
  squareBad P N ∪ smallBad P N ∪ mediumBad P N η ∪
    transitionBad P N η ∪ upperMiddleBad P N η ∪ upperTailBad P N η

lemma membership_overBranches {S : Finset ℕ} {B : Finset (Fin 4)}
    {f : ℕ → Fin 4 → Finset ℕ} {p : ℕ} {b : Fin 4} {u : ℕ}
    (hp : p ∈ S) (hb : b ∈ B) (hu : u ∈ f p b) :
    u ∈ overBranches S B f :=
  mem_biUnion.mpr ⟨p, hp, mem_biUnion.mpr ⟨b, hb, hu⟩⟩

lemma membership_bandBad {P N p u : ℕ} {α β : ℝ} {B : Finset (Fin 4)} {b : Fin 4}
    (hN : 0 < N) (he : p ∈ eligible P N) (hb : b ∈ B) (hu : u ∈ branchBad P N p b)
    (hl : (N : ℝ) ^ α < p) (hh : (p : ℝ) ≤ (N : ℝ) ^ β) :
    u ∈ bandBad P N α β B :=
  membership_overBranches (mem_inter.mpr ⟨he,
    (mem_primeBand hN).mpr ⟨(eligible_info he).1, hl, hh⟩⟩) hb hu

lemma medium_cover {N p : ℕ} {η : ℝ}
    (hl : (N : ℝ) ^ mediumExp η 81 < p)
    (hh : (p : ℝ) ≤ (N : ℝ) ^ mediumExp η 4) :
    ∃ j ∈ mediumIndices,
      (N : ℝ) ^ mediumExp η (j + 1) < p ∧ (p : ℝ) ≤ (N : ℝ) ^ mediumExp η j := by
  classical
  let s := mediumIndices.filter (fun j => (p : ℝ) ≤ (N : ℝ) ^ mediumExp η j)
  have hs : s.Nonempty := ⟨4, mem_filter.mpr ⟨by decide, hh⟩⟩
  let j := s.max' hs
  have hj : j ∈ s := max'_mem _ _
  obtain ⟨hjm, hjp⟩ := mem_filter.mp hj
  refine ⟨j, hjm, ?_, hjp⟩
  have hb := mem_Icc.mp hjm
  by_cases h : j = 80
  · simpa [h] using hl
  · by_contra! h'
    have hm : j + 1 ∈ s := mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h'⟩
    have hmax : j + 1 ≤ j := le_max' _ _ hm
    omega

lemma passes_outside {P N u : ℕ} (hP : 416 ≤ P)
    {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 1000)
    (hlarge : (10 : ℝ) * (branchBound P : ℝ) ≤ (N : ℝ) ^ (2 * η))
    (hhuge : (branchBound P : ℝ) ≤ (N : ℝ) ^ η)
    (hu : u < N) (hu' : u ∉ excluded P N η) :
    passes (family (parameter P u)) := by
  classical
  let t := parameter P u
  let n := family t
  refine ⟨by dsimp [n, family]; omega, ?_⟩
  intro p hmem
  change p ∈ (shiftProduct n).primeFactors at hmem
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hmem
  by_cases hpP : p ≤ P
  · exact fixed_primes_safe hP hp hpP hd
  have hpP' : P < p := Nat.lt_of_not_ge hpP
  have h7 : 7 ≤ p := by omega
  obtain ⟨b, hb⟩ := exists_branch hp hd
  have hbN := branch_le_bound (P := P) hu b
  have he : p ∈ eligible P N := mem_filter.mpr
    ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (branch_pos b t) hb).trans hbN, hp⟩, hpP'⟩
  have hno : ¬p ^ 2 ∣ branch b t := by
    intro hd'
    apply hu'
    have hU : u ∈ squareBad P N := membership_overBranches he (mem_univ b)
      (show u ∈ divisible P N p 2 b from mem_filter.mpr ⟨mem_range.mpr hu, hd'⟩)
    unfold excluded
    simp [hU]
  have hv := val_one_of_no_sq hp (branch_pos b t).ne' hb hno
  change 2 * (shiftProduct n).factorization p ≤ (carries n p).card
  rw [val_eq_branch hp h7 hb, hv, mul_one]
  have hfirst := first_carry hp h7 hd
  by_contra! hbad
  have honly : onlyFirst n p := by
    intro i hi
    by_contra! h
    exact hbad.not_ge (two_of_carry hfirst (by omega) hi)
  have huB : u ∈ branchBad P N p b := mem_filter.mpr ⟨mem_range.mpr hu, hb, honly⟩
  have hn : 0 < N := by omega
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < N := by positivity
  by_cases hsmall : 40 ≤ p.log N
  · have hpS : p ∈ (eligible P N).filter (fun p => 40 ≤ p.log N) :=
      mem_filter.mpr ⟨he, hsmall⟩
    have hU : u ∈ smallBad P N := membership_overBranches hpS (mem_univ b) huB
    exact hu' (by unfold excluded; simp [hU])
  have hl : (N : ℝ) ^ mediumExp η 81 < p := by
    by_contra! he
    have ham : mediumExp η 81 * 40 ≤ 1 := by unfold mediumExp; norm_num; linarith
    have hb' : (p : ℝ) ^ 40 ≤ N := calc
      _ ≤ ((N : ℝ) ^ mediumExp η 81) ^ 40 := pow_le_pow_left₀ (by positivity) he 40
      _ = (N : ℝ) ^ (mediumExp η 81 * 40) :=
        (Real.rpow_mul_natCast hn₀.le (mediumExp η 81) 40).symm
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn₁ ham
      _ = _ := Real.rpow_one _
    exact hsmall ((Nat.le_log_iff_pow_le hp.one_lt hn.ne').mpr (by exact_mod_cast hb'))
  by_cases hm : (p : ℝ) ≤ (N : ℝ) ^ mediumExp η 4
  · obtain ⟨j, hj, hjl, hjh⟩ := medium_cover hl hm
    have hU : u ∈ mediumBad P N η :=
      mem_biUnion.mpr ⟨j, hj, membership_bandBad hn he (mem_univ b) huB hjl hjh⟩
    exact hu' (by unfold excluded; simp [hU])
  have hmid : (N : ℝ) ^ ((1 : ℝ) / 2 - η) < p := by
    have he : mediumExp η 4 = 1 / 2 - η := by norm_num [mediumExp]
    rw [← he]
    exact lt_of_not_ge hm
  by_cases ht : (p : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + η)
  · have hU : u ∈ transitionBad P N η := membership_bandBad hn he (mem_univ b) huB hmid ht
    exact hu' (by unfold excluded; simp [hU])
  have hpl : (N : ℝ) ^ ((1 : ℝ) / 2 + η) < p := lt_of_not_ge ht
  have hql : 10 * (6 * t + 8) ≤ p ^ 2 := by
    have hl : 6 * t + 8 ≤ branchBound P * N := branch_le_bound hu (3 : Fin 4)
    have hle : (10 : ℝ) * (6 * (t : ℝ) + 8) ≤ (p : ℝ) ^ 2 := calc
      _ ≤ (10 : ℝ) * ((branchBound P : ℝ) * N) := by
        gcongr
        exact_mod_cast hl
      _ = (10 : ℝ) * (branchBound P : ℝ) * N := by ring
      _ ≤ (N : ℝ) ^ (2 * η) * N := mul_le_mul_of_nonneg_right hlarge hn₀.le
      _ = (N : ℝ) ^ (2 * ((1 : ℝ) / 2 + η)) := by
        rw [← Real.rpow_add_one hn₀.ne']
        congr 1
        ring
      _ = ((N : ℝ) ^ ((1 : ℝ) / 2 + η)) ^ 2 := by
        rw [show (2 : ℝ) * (1 / 2 + η) = (1 / 2 + η) * (2 : ℕ) by ring,
          Real.rpow_mul_natCast hn₀.le]
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hn₀.le _) hpl.le _
    exact_mod_cast hle
  have hb0 : b = 0 := by
    by_contra h
    have huD : p ∣ 6 * t + 6 ∨ p ∣ 6 * t + 3 ∨ p ∣ 6 * t + 8 := by
      fin_cases b
      · contradiction
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hb)
    have hn2 := large_prime_second_carry hp h7 hql huD
    exact (by decide : ¬(2 : ℕ) ≤ 1) (honly 2 hn2)
  have hb' : b ∈ firstBranch := mem_singleton.mpr hb0
  by_cases htop : (p : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3 - η)
  · have hU : u ∈ upperMiddleBad P N η := membership_bandBad hn he hb' huB hpl htop
    exact hu' (by unfold excluded; simp [hU])
  · have hre : (p : ℝ) ≤ (N : ℝ) ^ (1 + η) := calc
      _ ≤ (branchBound P : ℝ) * N := by exact_mod_cast (eligible_info he).2.2
      _ ≤ (N : ℝ) ^ η * N := mul_le_mul_of_nonneg_right hhuge hn₀.le
      _ = _ := by rw [← Real.rpow_add_one hn₀.ne', add_comm η 1]
    have hU : u ∈ upperTailBad P N η :=
      membership_bandBad hn he hb' huB (lt_of_not_ge htop) hre
    exact hu' (by unfold excluded; simp [hU])

end OMA.QuadraticCarry

namespace OMA.QuadraticCarry

open Filter Topology Finset

noncomputable def exclusionMajorant (P N : ℕ) (η : ℝ) : ℝ :=
  (4 / (P : ℝ) + 4 * primeDensityError P N) + 1 / 200 +
    mediumDensity P N η +
    4 * (bandMass N (1 / 2 - η) (1 / 2 + η) + primeDensityError P N) +
    (1 / 2 + η) * (bandMass N (1 / 2 + η) (2 / 3 - η) + primeDensityError P N) +
    (bandMass N (2 / 3 - η) (1 + η) + primeDensityError P N)

lemma normalized_union_le (N : ℕ) (s t : Finset ℕ) :
    ((s ∪ t).card : ℝ) / N ≤ (s.card : ℝ) / N + (t.card : ℝ) / N := by
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_union_le s t

lemma excluded_eventually (P : ℕ) (hP : 416 ≤ P) (η : ℝ) (hη : 0 < η) (hη' : η < 1 / 1000) :
    ∀ᶠ N : ℕ in atTop, ((excluded P N η).card : ℝ) / N ≤ exclusionMajorant P N η := by
  filter_upwards [medium_bad_eventually P hP η hη hη', upper_middle_eventually P hP η hη,
    eventually_gt_atTop (0 : ℕ)] with N hm hu hN
  have hs := square_bad_bound hP hN
  have hlow := small_bad_bound hP hN
  have ht : ((transitionBad P N η).card : ℝ) / N ≤
      4 * (bandMass N (1 / 2 - η) (1 / 2 + η) + primeDensityError P N) := by
    simpa [transitionBad] using band_bad_crude hP hN (1 / 2 - η) (1 / 2 + η) allBranches
  have hlast : ((upperTailBad P N η).card : ℝ) / N ≤
      bandMass N (2 / 3 - η) (1 + η) + primeDensityError P N := by
    simpa [upperTailBad] using band_bad_crude hP hN (2 / 3 - η) (1 + η) firstBranch
  unfold excluded exclusionMajorant
  refine (normalized_union_le N _ _).trans (add_le_add ?_ hlast)
  refine (normalized_union_le N _ _).trans (add_le_add ?_ hu)
  refine (normalized_union_le N _ _).trans (add_le_add ?_ ht)
  refine (normalized_union_le N _ _).trans (add_le_add ?_ hm)
  exact (normalized_union_le N _ _).trans (add_le_add hs hlow)

lemma majorant_tendsto (P : ℕ) (η : ℝ) (hη : 0 < η) (hη' : η < 1 / 1000) :
    Tendsto (fun N => exclusionMajorant P N η) atTop
      (𝓝 (4 / (P : ℝ) + 1 / 200 + budget η)) := by
  have he : Tendsto (primeDensityError P) atTop (𝓝 0) :=
    prime_count_error (branchBound P) (by unfold branchBound; positivity)
  have hb (α β : ℝ) (ha : 0 < α) (hab : α ≤ β) :
      Tendsto (fun N => bandMass N α β + primeDensityError P N) atTop (𝓝 (Real.log (β / α))) := by
    simpa [bandMass] using (band_tendsto α β ha hab).add he
  have hm : Tendsto (fun N => mediumDensity P N η) atTop
      (𝓝 (∑ j ∈ mediumIndices, 4 * (((1 / 2 : ℝ) ^ (j - 2) + η) *
        Real.log (mediumExp η j / mediumExp η (j + 1))))) := by
    unfold mediumDensity
    apply tendsto_finsetSum
    intro j hj
    have hh := medium_exp_bounds hη hη' hj
    exact ((hb _ _ hh.1 hh.2.1).const_mul _).const_mul _
  have h₀ : Tendsto (fun N => 4 / (P : ℝ) + 4 * primeDensityError P N + 1 / 200)
      atTop (𝓝 (4 / (P : ℝ) + 1 / 200)) := by
    simpa using ((tendsto_const_nhds (x := 4 / (P : ℝ))).add (he.const_mul (4 : ℝ))).add
      (tendsto_const_nhds (x := (1 / 200 : ℝ)))
  have ht := (hb (1 / 2 - η) (1 / 2 + η) (by linarith) (by linarith)).const_mul (4 : ℝ)
  have hu := (hb (1 / 2 + η) (2 / 3 - η) (by linarith) (by linarith)).const_mul (1 / 2 + η)
  have hf := hb (2 / 3 - η) (1 + η) (by linarith) (by linarith)
  have htend := (((h₀.add hm).add ht).add hu).add hf
  convert htend using 2
  · rfl
  · unfold budget
    ring

lemma eventual_large_thresholds (P : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      (10 : ℝ) * (branchBound P : ℝ) ≤ (N : ℝ) ^ (2 * η) ∧
      (branchBound P : ℝ) ≤ (N : ℝ) ^ η := by
  have hg (x : ℝ) (hx : 0 < x) : Tendsto (fun N : ℕ => (N : ℝ) ^ x) atTop atTop :=
    (tendsto_rpow_atTop hx).comp tendsto_natCast_atTop_atTop
  exact ((tendsto_atTop.1 (hg _ (by positivity))) _).and ((tendsto_atTop.1 (hg _ hη)) _)

lemma family_parameter_ge (P u : ℕ) : u ≤ family (parameter P u) := by
  have h₁ : u ≤ P.factorial * u := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
  have h₂ : parameter P u ≤ 11 * parameter P u := Nat.le_mul_of_pos_left _ (by decide)
  unfold family
  unfold parameter at *
  omega

lemma infinite_good : {n : ℕ | passes n}.Infinite := by
  obtain ⟨η, hη, hη', hb⟩ := choose_margin
  let P : ℕ := 10000
  have hP : 416 ≤ P := by decide
  have hfinal : 4 / (P : ℝ) + 1 / 200 + budget η < 997 / 1000 := by
    dsimp [P]
    linarith
  have hm := (majorant_tendsto P η hη hη').eventually_lt_const hfinal
  have hE := excluded_eventually P hP η hη hη'
  have hL := eventual_large_thresholds P hη
  apply Set.infinite_of_forall_exists_gt
  intro T
  obtain ⟨N, ⟨⟨hN, hNlarge⟩, hQ⟩, hZ⟩ :=
    (((eventually_ge_atTop ((T + 1) * 1000)).and hL).and hE).and hm |>.exists
  have hN0 : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by positivity
  have hsmall := (div_lt_iff₀ hN').mp (hQ.trans_lt hZ)
  have hsize : (excluded P N η ∪ range (T + 1)).card < (range N).card := by
    rw [card_range]
    have hTN : (T : ℝ) + 1 ≤ (N : ℝ) / 1000 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)).mpr
      exact_mod_cast hN
    have hc := card_union_le (excluded P N η) (range (T + 1))
    rw [card_range] at hc
    have hc' : ((excluded P N η ∪ range (T + 1)).card : ℝ) ≤
        (excluded P N η).card + ((T : ℝ) + 1) := by exact_mod_cast hc
    exact_mod_cast (show ((excluded P N η ∪ range (T + 1)).card : ℝ) < N by
      linarith)
  obtain ⟨u, hu, hnu⟩ := exists_mem_notMem_of_card_lt_card hsize
  have hnot : u ∉ excluded P N η := fun h => hnu (mem_union.mpr (Or.inl h))
  have huT : T < u := by
    have hnot' : u ∉ range (T + 1) := fun h => hnu (mem_union.mpr (Or.inr h))
    rw [mem_range] at hnot'
    omega
  exact ⟨family (parameter P u),
    passes_outside hP hη hη' hNlarge.1 hNlarge.2 (mem_range.mp hu) hnot,
    huT.trans_le (family_parameter_ge P u)⟩

end OMA.QuadraticCarry

-- Credit: @MrSeizy
theorem OMA.solution : OMA.R_Erdos727_erdos_727_variants_k_2_R1.H3 := by
  exact OMA.QuadraticCarry.H3_of_infinite_passes OMA.QuadraticCarry.infinite_good
