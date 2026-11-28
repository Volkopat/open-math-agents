import OMAReductions.R_Erdos120_erdos_120_R1

/-!
# Proof of `Erdos120.erdos_120.R1.H1` (Falconer 1984 / Eigen 1985)

Given a strictly decreasing positive null sequence `a : ℕ → ℝ` with `a (n + 1) / a n → 1`,
we construct a measurable set `E ⊆ [0, 1]` of positive Lebesgue measure containing no
non-degenerate affine copy `{c * a n + d | n : ℕ}` (`c ≠ 0`).

At each stage `m : ℕ`, set `γ m = (1 / 2) ^ (m + 4)`, choose `K m` so that
`1 - γ m < a (n + 1) / a n` for all `n ≥ K m`, and choose a grid size `N m ≥ m + 1` with
`2 * (m + 1) / N m ≤ a (K m)`. Remove from `[0, 1]` the open neighborhoods
`(k / N m - γ m / N m, k / N m + γ m / N m)` for all `k ∈ {0, …, N m}` and all `m : ℕ`.
Then:
1. Each stage removes measure at most `(N m + 1) * (2 * γ m / N m) ≤ 4 * γ m = (1 / 2) ^ (m + 2)`,
   so the union of all removed sets has measure at most `1 / 2`, giving `volume E > 0`.
2. `E` is symmetric under `x ↦ 1 - x`, reducing any affine copy to `c > 0`.
3. For large `m`, the open gap `(u, v)` around `k / N m` with `k = ⌊d * N m⌋₊ + 1` sits
   strictly to the right of `d` with `v - d < 2 / N m < c * a 0` and `(v - u) / (v - d) > γ m`.
   Choosing the smallest `n + 1` with `c * a (n + 1) < v - d` forces `n ≥ K m` and hence
   `c * a (n + 1) + d ∈ (u, v) ⊆ Eᶜ`, contradiction.
-/

namespace OMA.P_Erdos120_H1

open Filter Topology MeasureTheory Set

private noncomputable def gamma (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (m + 4)

private lemma gamma_pos (m : ℕ) : 0 < gamma m := by
  unfold gamma
  positivity

private lemma gamma_lt_one (m : ℕ) : gamma m < 1 := by
  unfold gamma
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

private lemma exists_K {a : ℕ → ℝ} (hrat : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1))
    (m : ℕ) : ∃ K : ℕ, ∀ n ≥ K, 1 - gamma m < a (n + 1) / a n := by
  have h := Metric.tendsto_atTop.mp hrat (gamma m) (gamma_pos m)
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n hn => ?_⟩
  have h1 := hK n hn
  rw [Real.dist_eq, abs_lt] at h1
  linarith

private noncomputable def Kseq {a : ℕ → ℝ}
    (hrat : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1)) (m : ℕ) : ℕ :=
  Classical.choose (exists_K hrat m)

private lemma Kseq_spec {a : ℕ → ℝ}
    (hrat : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1)) (m : ℕ) :
    ∀ n ≥ Kseq hrat m, 1 - gamma m < a (n + 1) / a n :=
  Classical.choose_spec (exists_K hrat m)

private noncomputable def Nseq {a : ℕ → ℝ}
    (hrat : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1)) (m : ℕ) : ℕ :=
  max (m + 1) (Nat.ceil (2 * ((m : ℝ) + 1) / a (Kseq hrat m)))

private lemma m_add_one_le_Nseq {a : ℕ → ℝ}
    (hrat : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1)) (m : ℕ) :
    m + 1 ≤ Nseq hrat m :=
  le_max_left _ _

private lemma Nseq_pos {a : ℕ → ℝ}
    (hrat : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1)) (m : ℕ) :
    (0 : ℝ) < (Nseq hrat m : ℝ) := by
  have h : 1 ≤ Nseq hrat m := le_trans (Nat.succ_le_succ (Nat.zero_le m)) (m_add_one_le_Nseq hrat m)
  exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one h)

private lemma two_div_Nseq_le {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n)
    (hrat : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1)) (m : ℕ) :
    2 * ((m : ℝ) + 1) / (Nseq hrat m : ℝ) ≤ a (Kseq hrat m) := by
  have hrpos : 0 < a (Kseq hrat m) := hpos _
  have hNpos : (0 : ℝ) < (Nseq hrat m : ℝ) := Nseq_pos hrat m
  have hceil : 2 * ((m : ℝ) + 1) / a (Kseq hrat m) ≤ (Nseq hrat m : ℝ) := by
    have hle : Nat.ceil (2 * ((m : ℝ) + 1) / a (Kseq hrat m)) ≤ Nseq hrat m :=
      le_max_right (m + 1) (Nat.ceil (2 * ((m : ℝ) + 1) / a (Kseq hrat m)))
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hle)
  rw [div_le_iff₀ hNpos]
  rw [div_le_iff₀ hrpos] at hceil
  linarith

private def gap (N : ℕ) (g : ℝ) (k : ℕ) : Set ℝ :=
  Ioo ((k : ℝ) / (N : ℝ) - g / (N : ℝ)) ((k : ℝ) / (N : ℝ) + g / (N : ℝ))

private def stageU (N : ℕ) (g : ℝ) : Set ℝ :=
  ⋃ k : Fin (N + 1), gap N g k.1

private lemma isOpen_stageU (N : ℕ) (g : ℝ) : IsOpen (stageU N g) :=
  isOpen_iUnion fun _ => isOpen_Ioo

private lemma measurableSet_stageU (N : ℕ) (g : ℝ) : MeasurableSet (stageU N g) :=
  (isOpen_stageU N g).measurableSet

private lemma stageU_symm {N : ℕ} {g x : ℝ} (hx : x ∈ stageU N g) :
    1 - x ∈ stageU N g := by
  rw [stageU, mem_iUnion] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  refine ⟨⟨N - k.1, by omega⟩, ?_⟩
  simp only [gap, mem_Ioo] at hk ⊢
  have hsub : ((N - k.1 : ℕ) : ℝ) = (N : ℝ) - (k.1 : ℝ) :=
    Nat.cast_sub (Nat.lt_succ_iff.mp k.2)
  rw [hsub]
  by_cases hN0 : N = 0
  · subst hN0
    simp only [Nat.cast_zero, div_zero, sub_zero, add_zero] at hk
    exact False.elim (lt_asymm hk.1 hk.2)
  · have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
    have hdiv : ((N : ℝ) - (k.1 : ℝ)) / (N : ℝ) = 1 - (k.1 : ℝ) / (N : ℝ) := by
      field_simp [hNne]
    rw [hdiv]
    constructor <;> linarith

private lemma volume_stageU_le {N : ℕ} (hN : 1 ≤ N) {g : ℝ} (hg : 0 < g) :
    volume (stageU N g) ≤ ENNReal.ofReal (4 * g) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have h1 : volume (stageU N g) ≤ ∑ k : Fin (N + 1), volume (gap N g k.1) := by
    unfold stageU
    exact measure_iUnion_fintype_le volume _
  have hgap : ∀ k : Fin (N + 1), volume (gap N g k.1) = ENNReal.ofReal (2 * g / (N : ℝ)) := by
    intro k
    unfold gap
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hsum : (∑ k : Fin (N + 1), volume (gap N g k.1)) =
      ENNReal.ofReal (((N : ℝ) + 1) * (2 * g / (N : ℝ))) := by
    simp only [hgap, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast (N + 1), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    push_cast
    rfl
  have hle : ((N : ℝ) + 1) * (2 * g / (N : ℝ)) ≤ 4 * g := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hratio : ((N : ℝ) + 1) / (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hNpos]
      linarith
    calc ((N : ℝ) + 1) * (2 * g / (N : ℝ))
        = 2 * g * (((N : ℝ) + 1) / (N : ℝ)) := by ring
      _ ≤ 2 * g * 2 := by nlinarith
      _ = 4 * g := by ring
  exact le_trans h1 (by rw [hsum]; exact ENNReal.ofReal_le_ofReal hle)

private lemma tsum_half_shift :
    (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 2)) = 1 / 2 := by
  have h1 : (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 2)) = fun m : ℕ => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ m := by
    funext m
    rw [pow_add]
    ring
  rw [h1, tsum_mul_left, tsum_geometric_two]
  norm_num

private lemma summable_half_shift : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 2)) := by
  have h1 : (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 2)) = fun m : ℕ => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ m := by
    funext m
    rw [pow_add]
    ring
  rw [h1]
  exact (summable_geometric_two).mul_left (1 / 4 : ℝ)

private lemma no_pos_affine_copy {a : ℕ → ℝ} (ha : StrictAnti a) (hpos : ∀ n, 0 < a n)
    (hlim : Tendsto a atTop (𝓝 0))
    (hrat : Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1))
    {c d : ℝ} (hc : 0 < c)
    (hsub : ∀ n : ℕ, c * a n + d ∈ Icc (0 : ℝ) 1 \ ⋃ m : ℕ, stageU (Nseq hrat m) (gamma m)) :
    False := by
  set U := ⋃ m : ℕ, stageU (Nseq hrat m) (gamma m)
  have hlim_seq : Tendsto (fun n => c * a n + d) atTop (𝓝 d) := by
    have h1 : Tendsto (fun n => c * a n) atTop (𝓝 (c * 0)) := hlim.const_mul c
    simpa using h1.add_const d
  have hd_nonneg : 0 ≤ d :=
    ge_of_tendsto hlim_seq (Eventually.of_forall fun n => (hsub n).1.1)
  have hd_lt_one : d < 1 := by
    have h0 : c * a 0 + d ≤ 1 := (hsub 0).1.2
    have hca0 : 0 < c * a 0 := mul_pos hc (hpos 0)
    linarith
  have hd_not_mem : ∀ m : ℕ, d ∉ stageU (Nseq hrat m) (gamma m) := by
    intro m hdm
    have hopen : IsOpen (stageU (Nseq hrat m) (gamma m)) := isOpen_stageU _ _
    have hev : ∀ᶠ n in atTop, c * a n + d ∈ stageU (Nseq hrat m) (gamma m) :=
      hlim_seq.eventually (hopen.mem_nhds hdm)
    obtain ⟨n, hn⟩ := hev.exists
    exact (hsub n).2 (mem_iUnion.mpr ⟨m, hn⟩)
  obtain ⟨m1, hm1⟩ := exists_nat_gt (1 / c)
  obtain ⟨m2, hm2⟩ := exists_nat_gt (2 / (c * a 0))
  set m := max m1 m2
  have hm_c : 1 / c ≤ (m : ℝ) + 1 := by
    have h1 : (m1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_left m1 m2
    linarith
  have hm_a0 : 2 / (c * a 0) < (m : ℝ) + 1 := by
    have h2 : (m2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_right m1 m2
    linarith
  set N := Nseq hrat m
  set g := gamma m
  have hNpos : (0 : ℝ) < (N : ℝ) := Nseq_pos hrat m
  have hgpos : 0 < g := gamma_pos m
  have hglt : g < 1 := gamma_lt_one m
  have hm_le_N : (m : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast m_add_one_le_Nseq hrat m
  have hdN_lt : d * (N : ℝ) < (N : ℝ) := by nlinarith
  have hfloor_lt : Nat.floor (d * (N : ℝ)) < N :=
    (Nat.floor_lt (mul_nonneg hd_nonneg (le_of_lt hNpos))).mpr hdN_lt
  set k : ℕ := Nat.floor (d * (N : ℝ)) + 1
  have hk_lt : k < N + 1 := Nat.succ_lt_succ hfloor_lt
  set u : ℝ := (k : ℝ) / (N : ℝ) - g / (N : ℝ)
  set v : ℝ := (k : ℝ) / (N : ℝ) + g / (N : ℝ)
  have hkd_gt : d < (k : ℝ) / (N : ℝ) := by
    rw [lt_div_iff₀ hNpos]
    have := Nat.lt_floor_add_one (d * (N : ℝ))
    simpa [k] using this
  have hkd_le : (k : ℝ) / (N : ℝ) - d ≤ 1 / (N : ℝ) := by
    have hfl : (Nat.floor (d * (N : ℝ)) : ℝ) ≤ d * (N : ℝ) :=
      Nat.floor_le (mul_nonneg hd_nonneg (le_of_lt hNpos))
    have hk_le : (k : ℝ) ≤ d * (N : ℝ) + 1 := by
      simp only [k, Nat.cast_add, Nat.cast_one]
      linarith
    have hdiv : (k : ℝ) / (N : ℝ) ≤ d + 1 / (N : ℝ) := by
      rw [div_le_iff₀ hNpos]
      have : (d + 1 / (N : ℝ)) * (N : ℝ) = d * (N : ℝ) + 1 := by
        field_simp [ne_of_gt hNpos]
      linarith
    linarith
  have hd_le_u : d ≤ u := by
    by_contra hlt
    push Not at hlt
    have hdu : d ∈ gap N g k := by
      refine ⟨hlt, ?_⟩
      have : 0 < g / (N : ℝ) := div_pos hgpos hNpos
      linarith
    exact hd_not_mem m (mem_iUnion.mpr ⟨⟨k, hk_lt⟩, hdu⟩)
  have hv_gt_d : 0 < v - d := by
    have : 0 < g / (N : ℝ) := div_pos hgpos hNpos
    linarith
  have hv_lt_2N : v - d < 2 / (N : ℝ) := by
    have hgN : g / (N : ℝ) < 1 / (N : ℝ) := div_lt_div_of_pos_right hglt hNpos
    have h1 : v - d = ((k : ℝ) / (N : ℝ) - d) + g / (N : ℝ) := by ring
    have h2 : 1 / (N : ℝ) + 1 / (N : ℝ) = 2 / (N : ℝ) := by ring
    linarith
  have h2N_lt_ca0 : 2 / (N : ℝ) < c * a 0 := by
    have hca0 : 0 < c * a 0 := mul_pos hc (hpos 0)
    have h1 : 2 < (c * a 0) * ((m : ℝ) + 1) := by
      have := (div_lt_iff₀ hca0).mp hm_a0
      linarith
    rw [div_lt_iff₀ hNpos]
    nlinarith
  have hv_lt_ca0 : v - d < c * a 0 := lt_trans hv_lt_2N h2N_lt_ca0
  have hex_lt : ∃ n : ℕ, c * a n < v - d := by
    have h1 : Tendsto (fun n => c * a n) atTop (𝓝 0) := by
      simpa using hlim.const_mul c
    have hev : ∀ᶠ n in atTop, c * a n < v - d :=
      h1.eventually (Iio_mem_nhds hv_gt_d)
    exact hev.exists
  classical
  set n0 := Nat.find hex_lt
  have hn0_lt : c * a n0 < v - d := Nat.find_spec hex_lt
  have hn0_ne_zero : n0 ≠ 0 := by
    intro h0
    rw [h0] at hn0_lt
    linarith
  obtain ⟨n, hn_eq⟩ := Nat.exists_eq_succ_of_ne_zero hn0_ne_zero
  have h_succ_lt : c * a (n + 1) < v - d := by simpa [hn_eq] using hn0_lt
  have h_ge : v - d ≤ c * a n := by
    have hnot : ¬ c * a n < v - d := Nat.find_min hex_lt (by omega)
    exact not_lt.mp hnot
  have ha_succ_lt : a (n + 1) < a (Kseq hrat m) := by
    have h1 : a (n + 1) < (v - d) / c := (lt_div_iff₀ hc).mpr (by linarith)
    have h2 : (v - d) / c < 2 / ((N : ℝ) * c) := by
      have := div_lt_div_of_pos_right hv_lt_2N hc
      simpa [div_div] using this
    have h3 : 2 / ((N : ℝ) * c) ≤ 2 * ((m : ℝ) + 1) / (N : ℝ) := by
      have h2Npos : (0 : ℝ) < 2 / (N : ℝ) := div_pos (by norm_num) hNpos
      calc 2 / ((N : ℝ) * c)
          = (2 / (N : ℝ)) * (1 / c) := by ring
        _ ≤ (2 / (N : ℝ)) * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_left hm_c (le_of_lt h2Npos)
        _ = 2 * ((m : ℝ) + 1) / (N : ℝ) := by ring
    exact lt_of_lt_of_le (lt_trans h1 h2) (le_trans h3 (two_div_Nseq_le hpos hrat m))
  have hK_le_n : Kseq hrat m ≤ n := by
    have hlt : Kseq hrat m < n + 1 := by
      by_contra hle
      push Not at hle
      have : a (Kseq hrat m) ≤ a (n + 1) := ha.antitone hle
      linarith
    omega
  have hrat_n : 1 - g < a (n + 1) / a n := Kseq_spec hrat m n hK_le_n
  have h_ca_succ_gt : (1 - g) * (v - d) < c * a (n + 1) := by
    have han_pos : 0 < a n := hpos n
    have hcan_pos : 0 < c * a n := mul_pos hc han_pos
    have h1 : (1 - g) * (c * a n) < c * a (n + 1) := by
      have hmul := mul_lt_mul_of_pos_right hrat_n hcan_pos
      have heq : a (n + 1) / a n * (c * a n) = c * a (n + 1) := by
        field_simp [ne_of_gt han_pos]
      rwa [heq] at hmul
    have h1mg : 0 < 1 - g := by linarith
    have h2 : (1 - g) * (v - d) ≤ (1 - g) * (c * a n) :=
      mul_le_mul_of_nonneg_left h_ge (le_of_lt h1mg)
    exact lt_of_le_of_lt h2 h1
  have hgv_lt : g * (v - d) < v - u := by
    have hvu : v - u = 2 * g / (N : ℝ) := by ring
    rw [hvu]
    calc g * (v - d)
        < g * (2 / (N : ℝ)) := mul_lt_mul_of_pos_left hv_lt_2N hgpos
      _ = 2 * g / (N : ℝ) := by ring
  have hu_lt : u < c * a (n + 1) + d := by linarith
  have hv_gt : c * a (n + 1) + d < v := by linarith
  have hin_gap : c * a (n + 1) + d ∈ gap N g k := ⟨hu_lt, hv_gt⟩
  exact (hsub (n + 1)).2 (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨⟨k, hk_lt⟩, hin_gap⟩⟩)

theorem h1_proof : OMA.R_Erdos120_erdos_120_R1.H1 := by
  intro a ha hpos hlim hrat
  set U : Set ℝ := ⋃ m : ℕ, stageU (Nseq hrat m) (gamma m)
  set E : Set ℝ := Icc (0 : ℝ) 1 \ U
  refine ⟨E, ?_, ?_, ?_⟩
  · exact measurableSet_Icc.diff (MeasurableSet.iUnion fun m => measurableSet_stageU _ _)
  · have hU_le : volume U ≤ ENNReal.ofReal (1 / 2) := by
      calc volume U
          ≤ ∑' m : ℕ, volume (stageU (Nseq hrat m) (gamma m)) := measure_iUnion_le _
        _ ≤ ∑' m : ℕ, ENNReal.ofReal (4 * gamma m) := by
            refine ENNReal.tsum_le_tsum fun m => ?_
            have hN1 : 1 ≤ Nseq hrat m :=
              le_trans (Nat.succ_le_succ (Nat.zero_le m)) (m_add_one_le_Nseq hrat m)
            exact volume_stageU_le hN1 (gamma_pos m)
        _ = ∑' m : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + 2)) := by
            congr 1
            funext m
            congr 1
            unfold gamma
            rw [show m + 4 = (m + 2) + 2 by omega, pow_add]
            ring
        _ = ENNReal.ofReal (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 2)) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) summable_half_shift).symm
        _ = ENNReal.ofReal (1 / 2) := by rw [tsum_half_shift]
    have hcov : Icc (0 : ℝ) 1 ⊆ E ∪ U := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inr hxU
      · exact Or.inl ⟨hx, hxU⟩
    have hone_le : (1 : ENNReal) ≤ volume E + ENNReal.ofReal (1 / 2) := by
      calc (1 : ENNReal)
          = volume (Icc (0 : ℝ) 1) := by simp [Real.volume_Icc]
        _ ≤ volume (E ∪ U) := measure_mono hcov
        _ ≤ volume E + volume U := measure_union_le E U
        _ ≤ volume E + ENNReal.ofReal (1 / 2) := add_le_add_right hU_le _
    by_contra hE0
    have hEeq : volume E = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hE0)
    rw [hEeq, zero_add] at hone_le
    have hlt : ENNReal.ofReal (1 / 2) < ENNReal.ofReal 1 :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
    rw [ENNReal.ofReal_one] at hlt
    exact not_le_of_gt hlt hone_le
  · intro c d hc hsub
    have hmem : ∀ n : ℕ, c * a n + d ∈ E := fun n => hsub ⟨a n, ⟨n, rfl⟩, rfl⟩
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · apply no_pos_affine_copy ha hpos hlim hrat (neg_pos.mpr hcneg) (d := 1 - d)
      intro n
      have hn := hmem n
      have heq : -c * a n + (1 - d) = 1 - (c * a n + d) := by ring
      rw [heq]
      refine ⟨⟨by linarith [hn.1.2], by linarith [hn.1.1]⟩, ?_⟩
      intro hU
      rw [mem_iUnion] at hU
      obtain ⟨m, hm⟩ := hU
      have hback := stageU_symm hm
      rw [sub_sub_cancel] at hback
      exact hn.2 (mem_iUnion.mpr ⟨m, hback⟩)
    · exact no_pos_affine_copy ha hpos hlim hrat hcpos hmem

end OMA.P_Erdos120_H1

theorem OMA.solution : OMA.R_Erdos120_erdos_120_R1.H1 :=
  OMA.P_Erdos120_H1.h1_proof
