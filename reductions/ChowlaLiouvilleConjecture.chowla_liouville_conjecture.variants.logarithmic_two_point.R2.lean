import FormalConjectures.Wikipedia.ChowlaLiouvilleConjecture

-- Reduction ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.logarithmic_two_point.R2 of Logarithmically Averaged Two-Point Chowla Theorem
-- Credit: @yuka30240
/-!
H1 gives recurrence along an arithmetic progression of positive shifts for
each subsequential correlation limit. Averaging on that progression pairs
one Liouville factor with a short progression mean. H2 bounds the latter in
ordinary average. One-sided Abel summation transfers the bound to logarithmic
weights, forcing every subsequential limit at a positive shift to vanish.
-/

namespace OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_logarithmic_two_point_R2

open Filter Topology Finset ArithmeticFunction

private lemma harmonic_real (N : ℕ) :
    (harmonic N : ℝ) = ∑ i ∈ range N, ((i : ℝ) + 1)⁻¹ := by
  simp [harmonic]

private lemma harmonic_top : Tendsto (fun N : ℕ ↦ (harmonic N : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun n => log_add_one_le_harmonic n)
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

/-- Positive shifts recur along a progression in every pointwise subsequential
limit. This is the consequence of uniform periodic approximation in
Tao and Teräväinen, Theorem 1.2(i), arXiv:1708.02610, needed here. -/
def H1 : Prop :=
  ∀ (u : ℕ → ℕ) (F : ℕ → ℝ), Tendsto u atTop atTop →
    (∀ h : ℕ, 0 < h → Tendsto (fun m ↦
      (∑ i ∈ range (u m), (liouville (i + 1) * liouville (i + 1 + h) : ℝ) / (i + 1 : ℝ)) /
        (harmonic (u m) : ℝ)) atTop (𝓝 (F h))) →
    ∀ a : ℕ, 0 < a → ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 0 < q ∧
      ∀ j : ℕ, |F (a + j * q) - F a| ≤ ε

/-- The one-point Liouville mean on some sufficiently long block of a fixed
progression is small on average over its starting point. For fixed q, residue
class detection by additive characters gives this from the modulated
short-interval estimate of Matomäki, Radziwiłł and Tao, Theorem 1.3
(arXiv:1503.05121). -/
def H2 : Prop :=
  ∀ a q : ℕ, 0 < q → ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, 0 < K ∧
    ∀ᶠ N : ℕ in atTop, (∑ i ∈ range N,
      |(∑ j ∈ range K, (liouville (i + 1 + (a + j * q)) : ℝ)) / K|) ≤ ε * N

/-- One-sided summation by parts. A bounded excess of the partial sums over a
linear function gives the same bounded excess over the harmonic sum. -/
lemma abel_bound (f : ℕ → ℝ) (c D : ℝ)
    (h : ∀ N : ℕ, (∑ i ∈ range N, f i) ≤ c * N + D) (N : ℕ) :
    (∑ i ∈ range N, f i / (i + 1 : ℝ)) ≤ c * (harmonic N : ℝ) + D := by
  let E (n : ℕ) := c * n + D - ∑ i ∈ range n, f i
  have hE (n : ℕ) : 0 ≤ E n := sub_nonneg.mpr (h n)
  have aux (n : ℕ) : (∑ i ∈ range n, f i / (i + 1 : ℝ)) + E n / (n + 1 : ℝ)
      ≤ c * (harmonic n : ℝ) + D := by
    induction n with
    | zero => simp [E]
    | succ n ih =>
      have step : E (n + 1) = E n + c - f n := by
        simp [E, sum_range_succ, mul_add]
        ring
      have hden : E (n + 1) / ((n : ℝ) + 1 + 1) ≤ E (n + 1) / (n + 1 : ℝ) :=
        div_le_div_of_nonneg_left (hE _) (by positivity) (by linarith)
      rw [sum_range_succ, harmonic_succ]
      push_cast
      calc
        _ ≤ (∑ i ∈ range n, f i / (i + 1 : ℝ)) + f n / (n + 1 : ℝ) +
            E (n + 1) / (n + 1 : ℝ) := by linarith only [hden]
        _ = (∑ i ∈ range n, f i / (i + 1 : ℝ)) + E n / (n + 1 : ℝ) +
            c / (n + 1 : ℝ) := by rw [step]; ring
        _ ≤ _ := by simp only [div_eq_mul_inv] at ih ⊢; linarith only [ih]
  exact (le_add_of_nonneg_right (div_nonneg (hE N) (by positivity))).trans (aux N)

private lemma harmonic_mean_bound (f : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ N : ℕ in atTop, (∑ i ∈ range N, f i) ≤ c * N) :
    ∀ᶠ N : ℕ in atTop,
      (∑ i ∈ range N, f i / (i + 1 : ℝ)) / (harmonic N : ℝ) ≤ 2 * c := by
  have bounded : ∀ᶠ N : ℕ in atTop, (∑ i ∈ range N, f i) - c * N ≤ 0 :=
    h.mono fun _ hi => sub_nonpos.mpr hi
  obtain ⟨D, hD⟩ := (isBoundedUnder_of_eventually_le bounded).bddAbove_range
  have h' (N : ℕ) : (∑ i ∈ range N, f i) ≤ c * N + D := by
    have := hD (Set.mem_range_self N)
    linarith
  filter_upwards [harmonic_top.eventually_gt_atTop 0,
    (harmonic_top.const_div_atTop D).eventually (gt_mem_nhds hc)] with N hN hsmall
  have hoff : D < c * (harmonic N : ℝ) := (div_lt_iff₀ hN).mp hsmall
  apply (div_le_iff₀ hN).mpr
  linarith [abel_bound f c D h' N]

private lemma abs_liouville_le (n : ℕ) : |(liouville n : ℝ)| ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · simp [liouville_apply hn, abs_pow]

private lemma corr_bound (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) (N h : ℕ) :
    |(∑ i ∈ range N, x (i + 1) * x (i + 1 + h) / (i + 1 : ℝ)) / (harmonic N : ℝ)| ≤ 1 := by
  have hsum : |∑ i ∈ range N, x (i + 1) * x (i + 1 + h) / (i + 1 : ℝ)| ≤ (harmonic N : ℝ) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [harmonic_real]
    apply sum_le_sum
    intro i _
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < i + 1), ← one_div]
    exact div_le_div_of_nonneg_right (by simpa using mul_le_mul (hx _) (hx _) (abs_nonneg _) zero_le_one) (by positivity)
  rw [abs_div, abs_of_nonneg ((abs_nonneg _).trans hsum)]
  by_cases hz : (harmonic N : ℝ) = 0
  · simp [hz]
  · apply (div_le_iff₀ (lt_of_le_of_ne ((abs_nonneg _).trans hsum) (Ne.symm hz))).mpr
    simpa using hsum

private lemma block_bound (x : ℕ → ℝ) (hx : ∀ n, |x n| ≤ 1) (a q K N : ℕ) :
    |(∑ j ∈ range K, (∑ i ∈ range N, x (i + 1) * x (i + 1 + (a + j * q)) / (i + 1 : ℝ)) /
      (harmonic N : ℝ)) / K| ≤
      (∑ i ∈ range N, |(∑ j ∈ range K, x (i + 1 + (a + j * q))) / K| / (i + 1 : ℝ)) /
      (harmonic N : ℝ) := by
  have heq : (∑ j ∈ range K, (∑ i ∈ range N,
      x (i + 1) * x (i + 1 + (a + j * q)) / (i + 1 : ℝ)) / (harmonic N : ℝ)) / K =
      (∑ i ∈ range N, x (i + 1) * ((∑ j ∈ range K, x (i + 1 + (a + j * q))) / K) /
        (i + 1 : ℝ)) / (harmonic N : ℝ) := by
    simp_rw [div_eq_mul_inv, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simp only [sum_mul]
    apply sum_congr rfl
    intro j _
    ring
  rw [heq, abs_div, abs_of_nonneg (by rw [harmonic_real]; positivity : 0 ≤ (harmonic N : ℝ))]
  apply div_le_div_of_nonneg_right _ (by rw [harmonic_real]; positivity)
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < i + 1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_of_le_one_left (abs_nonneg _) (hx _)

private lemma mean_close (F : ℕ → ℝ) (a q K : ℕ) (hK : 0 < K) {δ : ℝ}
    (h : ∀ j, |F (a + j * q) - F a| ≤ δ) :
    |(∑ j ∈ range K, F (a + j * q)) / K - F a| ≤ δ := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have heq : (∑ j ∈ range K, F (a + j * q)) / K - F a =
      (∑ j ∈ range K, (F (a + j * q) - F a)) / K := by
    rw [sum_sub_distrib]
    simp only [sum_const, card_range, nsmul_eq_mul]
    field_simp
  rw [heq, abs_div, abs_of_pos hKr, div_le_iff₀ hKr]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j ∈ range K, δ := sum_le_sum fun j _ => h j
    _ = _ := by simp [mul_comm]

private lemma harmonic_ratio :
    Tendsto (fun N : ℕ ↦ (harmonic N : ℝ) / Real.log N) atTop (𝓝 1) := by
  have ht : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (Real.tendsto_harmonic_sub_log.div_atTop ht).add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [ht.eventually_gt_atTop 0] with N hn
  field_simp
  ring

theorem main : H1 → H2 →
    type_of% @ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.logarithmic_two_point := by
  intro h1 h2 a ha
  let x (n : ℕ) : ℝ := liouville n
  let C (N h : ℕ) := (∑ i ∈ range N, x (i + 1) * x (i + 1 + h) / (i + 1 : ℝ)) /
    (harmonic N : ℝ)
  have hzero : Tendsto (fun N ↦ C N a) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro v hv
    have box := isCompact_univ_pi (fun _ : ℕ => isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    obtain ⟨F, _, w, hw, hF⟩ := box.tendsto_subseq (x := fun m => C (v m)) (by
      intro m h _
      exact abs_le.mp (corr_bound x abs_liouville_le _ _))
    let u := v ∘ w
    have hu : Tendsto u atTop atTop := hv.comp hw.tendsto_atTop
    have coord (h : ℕ) : Tendsto (fun m ↦ C (u m) h) atTop (𝓝 (F h)) :=
      tendsto_pi_nhds.mp hF h
    suffices hz : F a = 0 from ⟨w, hz ▸ coord a⟩
    by_contra hn
    let δ := |F a| / 4
    have hδ : 0 < δ := div_pos (abs_pos.mpr hn) (by norm_num)
    obtain ⟨q, hq, hrec⟩ := h1 u F hu (fun h _ => coord h) a ha δ hδ
    obtain ⟨K, hK, hshort⟩ := h2 a q hq δ hδ
    let B (g : ℕ → ℝ) := (∑ j ∈ range K, g (a + j * q)) / K
    have hlim : Tendsto (fun m ↦ B (C (u m))) atTop (𝓝 (B F)) :=
      (tendsto_finsetSum (range K) (fun j _ => coord (a + j * q))).div_const _
    have hsmall : |B F| ≤ 2 * δ := by
      apply le_of_tendsto hlim.abs
      refine hu.eventually (p := fun N => |B (C N)| ≤ 2 * δ) ?_
      filter_upwards [harmonic_mean_bound _ hδ hshort] with N hN
      exact (block_bound x abs_liouville_le a q K N).trans hN
    have hnear : |B F - F a| ≤ δ := mean_close F a q K hK hrec
    have htri : |F a| ≤ |B F - F a| + |B F| := by
      simpa [abs_sub_comm, add_comm] using abs_sub_le (F a) (B F) 0
    dsimp [δ] at hsmall hnear
    linarith only [hsmall, hnear, htri, abs_pos.mpr hn]
  have h := hzero.mul harmonic_ratio
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [harmonic_top.eventually_gt_atTop 0] with N hN
  let f (n : ℕ) := x n * x (n + a) / (n : ℝ)
  have hsum : (∑ i ∈ range N, f (i + 1)) = ∑ n ∈ Icc 1 N, f n := by
    rw [range_eq_Ico, sum_Ico_add' f 0 N (c := 1)]
    simp [Ico_add_one_right_eq_Icc]
  have hsum' : (∑ i ∈ range N, x (i + 1) * x (i + 1 + a) / (i + 1 : ℝ)) =
      ∑ n ∈ Icc 1 N, x n * x (n + a) / (n : ℝ) := by
    simpa only [f, Nat.cast_add, Nat.cast_one] using hsum
  dsimp only [C]
  rw [hsum']
  exact div_mul_div_cancel₀ (ne_of_gt hN)

end OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_logarithmic_two_point_R2
