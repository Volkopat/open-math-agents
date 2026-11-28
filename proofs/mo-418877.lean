import OMAStatements.S_mo_418877

-- Problem: Prove or disprove a mutual information inequality
-- Upstream: formal-conjectures statements/mo-418877.lean:0 (declaration OMA.S_mo_418877.main)
-- Credit: @artnoage (the owner of the agent is credited as the solver)
--
-- Disproof. Take n = 30 and the channel q(0) = 1, q(s) = 1 - ε for 1 ≤ s ≤ 4, q(s) = 0 for s ≥ 5
-- (the three-level step channel of @Denyven's description of the statement). For weights k ≥ 5 and
-- m = n - k binomial trials, with A = (1-p)^(m+1) and M = P(1 ≤ S ≤ 4), the output-zero probability
-- is Y = A + (1-ε) M and the information is h(Y) - h(ε) M.
-- * Weight 5 (m = 25): by the intermediate value theorem Y = 1/2 at some p₀ ≤ pb, where
--   M ≤ (1/2 - (1-pb)^26)/(1-ε) ≤ θ, so the capacity is at least log 2 - h(ε) θ.
-- * Weight 6 (m = 24): if |Y - 1/2| < δ then p ≥ pc (Y is antitone in p), hence
--   M ≥ 1/2 - δ - (1-pc)^25 ≥ θ + η; otherwise h(Y) ≤ h(1/2 + δ) ≤ log 2 - h(ε) once ε is small.
--   Either way the information is at most log 2 - h(ε)(θ + η).
-- Here pb = 82817/500000, pc = 343343/2000000, δ = 1/250000, η = 1/10^7, and ε ≤ 1/10^9 is
-- chosen by continuity of the binary entropy at 0.

open Finset Set Real OMA.S_mo_418877

namespace MO418877

noncomputable def q (ε : ℝ) (s : ℕ) : ℝ := if s = 0 then 1 else if s < 5 then 1 - ε else 0

noncomputable def M25 (p : ℝ) : ℝ :=
  (1-p)*(25*p*(1-p)^24 + 300*p^2*(1-p)^23 + 2300*p^3*(1-p)^22 + 12650*p^4*(1-p)^21)

noncomputable def M24 (p : ℝ) : ℝ :=
  (1-p)*(24*p*(1-p)^23 + 276*p^2*(1-p)^22 + 2024*p^3*(1-p)^21 + 10626*p^4*(1-p)^20)

noncomputable def F24 (p : ℝ) : ℝ :=
  (1-p)^24 + 24*p*(1-p)^23 + 276*p^2*(1-p)^22 + 2024*p^3*(1-p)^21 + 10626*p^4*(1-p)^20

lemma avg_red (n k : ℕ) (p : ℝ) (f : ℕ → ℝ) (hk : 5 ≤ k) (hm : 4 ≤ n - k)
    (hf : ∀ s, 5 ≤ s → f s = 0) :
    average n k p f = ∑ j ∈ range 5, binomialWeight (n - k) j p * ((1 - p) * f j) := by
  unfold average
  have h := Finset.sum_subset
    (f := fun j => binomialWeight (n - k) j p * ((1 - p) * f j + p * f (k + j)))
    (s₁ := range 5) (s₂ := range (n - k + 1))
    (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
    (fun x _ hx => by
      have h5 : 5 ≤ x := by simpa using hx
      simp [hf x h5, hf (k + x) (by omega)])
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [hf (k + j) (by omega)]
  ring

lemma info25 (ε p : ℝ) : information (q ε) 30 5 p
    = binEntropy ((1-p)^26 + (1-ε) * M25 p) - binEntropy ε * M25 p := by
  have c1 : Nat.choose 25 1 = 25 := by decide
  have c2 : Nat.choose 25 2 = 300 := by decide
  have c3 : Nat.choose 25 3 = 2300 := by decide
  have c4 : Nat.choose 25 4 = 12650 := by decide
  unfold information
  rw [avg_red 30 5 p (q ε) (by norm_num) (by norm_num) (fun s hs => by
        unfold q; rw [if_neg (by omega), if_neg (by omega)]),
      avg_red 30 5 p (fun s => binEntropy (q ε s)) (by norm_num) (by norm_num) (fun s hs => by
        unfold q; rw [if_neg (by omega), if_neg (by omega)]; simp)]
  have e1 : ∑ j ∈ range 5, binomialWeight (30 - 5) j p * ((1 - p) * q ε j)
      = (1-p)^26 + (1-ε) * M25 p := by
    simp [Finset.sum_range_succ, binomialWeight, q, M25, c1, c2, c3, c4]
    ring
  have e2 : ∑ j ∈ range 5, binomialWeight (30 - 5) j p * ((1 - p) * binEntropy (q ε j))
      = binEntropy ε * M25 p := by
    simp [Finset.sum_range_succ, binomialWeight, q, M25, c1, c2, c3, c4]
    ring
  rw [e1, e2]

lemma info24 (ε p : ℝ) : information (q ε) 30 6 p
    = binEntropy ((1-p)^25 + (1-ε) * M24 p) - binEntropy ε * M24 p := by
  have c1 : Nat.choose 24 1 = 24 := by decide
  have c2 : Nat.choose 24 2 = 276 := by decide
  have c3 : Nat.choose 24 3 = 2024 := by decide
  have c4 : Nat.choose 24 4 = 10626 := by decide
  unfold information
  rw [avg_red 30 6 p (q ε) (by norm_num) (by norm_num) (fun s hs => by
        unfold q; rw [if_neg (by omega), if_neg (by omega)]),
      avg_red 30 6 p (fun s => binEntropy (q ε s)) (by norm_num) (by norm_num) (fun s hs => by
        unfold q; rw [if_neg (by omega), if_neg (by omega)]; simp)]
  have e1 : ∑ j ∈ range 5, binomialWeight (30 - 6) j p * ((1 - p) * q ε j)
      = (1-p)^25 + (1-ε) * M24 p := by
    simp [Finset.sum_range_succ, binomialWeight, q, M24, c1, c2, c3, c4]
    ring
  have e2 : ∑ j ∈ range 5, binomialWeight (30 - 6) j p * ((1 - p) * binEntropy (q ε j))
      = binEntropy ε * M24 p := by
    simp [Finset.sum_range_succ, binomialWeight, q, M24, c1, c2, c3, c4]
    ring
  rw [e1, e2]

lemma M25_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ M25 p := by
  have : 0 ≤ 1 - p := by linarith
  unfold M25
  positivity

lemma M24_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ M24 p := by
  have : 0 ≤ 1 - p := by linarith
  unfold M24
  positivity

lemma F24_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ F24 p := by
  have : 0 ≤ 1 - p := by linarith
  unfold F24
  positivity

lemma F24_deriv (p : ℝ) : HasDerivAt F24 (-(212520 * p^4 * (1-p)^19)) p := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub 1
  have h0 : HasDerivAt (fun x : ℝ => x) 1 p := hasDerivAt_id p
  have h := ((((h1.fun_pow 24).fun_add ((h0.const_mul 24).fun_mul (h1.fun_pow 23))).fun_add
    (((h0.fun_pow 2).const_mul 276).fun_mul (h1.fun_pow 22))).fun_add
    (((h0.fun_pow 3).const_mul 2024).fun_mul (h1.fun_pow 21))).fun_add
    (((h0.fun_pow 4).const_mul 10626).fun_mul (h1.fun_pow 20))
  have hfun : F24 = fun x : ℝ => (1-x)^24 + 24*x*(1-x)^23 + 276*x^2*(1-x)^22
      + 2024*x^3*(1-x)^21 + 10626*x^4*(1-x)^20 := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  first
    | (norm_num; ring)
    | norm_num
    | ring

lemma F24_anti : AntitoneOn F24 (Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · exact fun x _ => (F24_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => (F24_deriv x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(F24_deriv x).deriv]
    have h1 : 0 ≤ 1 - x := by linarith [hx.2]
    have h2 : 0 ≤ x := hx.1.le
    have : 0 ≤ 212520 * x^4 * (1-x)^19 := by positivity
    linarith

lemma Y24_eq (ε p : ℝ) :
    (1-p)^25 + (1-ε) * M24 p = (1-ε) * ((1-p) * F24 p) + ε * (1-p)^25 := by
  unfold M24 F24
  ring

lemma Y24_le_one {ε p : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (1-p)^25 + (1-ε) * M24 p ≤ 1 := by
  rw [Y24_eq]
  have hp : 0 ≤ 1 - p := by linarith
  have hF : F24 p ≤ 1 := by
    have := F24_anti (Set.left_mem_Icc.2 zero_le_one) ⟨h0, h1⟩ h0
    simpa [F24] using this
  have hG : (1-p) * F24 p ≤ 1 := mul_le_one₀ (by linarith) (F24_nonneg h0 h1) hF
  have hA : (1-p)^25 ≤ 1 := pow_le_one₀ hp (by linarith)
  nlinarith

lemma Y24_low {ε p : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/1000000000) (h0 : 0 ≤ p)
    (hp : p ≤ 343343/2000000) :
    1/2 + 1/250000 ≤ (1-p)^25 + (1-ε) * M24 p := by
  rw [Y24_eq]
  have hp1 : p ≤ 1 := by linarith
  have hq : 0 ≤ 1 - p := by linarith
  have hF : F24 (343343/2000000) ≤ F24 p :=
    F24_anti ⟨h0, hp1⟩ ⟨by norm_num, by norm_num⟩ hp
  have hFc : 0 ≤ F24 (343343/2000000) := F24_nonneg (by norm_num) (by norm_num)
  have hG : (1 - 343343/2000000) * F24 (343343/2000000) ≤ (1-p) * F24 p :=
    mul_le_mul (by linarith) hF hFc hq
  have num : 1/2 + 1/250000 ≤ (1 - 1/1000000000) * ((1 - 343343/2000000) * F24 (343343/2000000)) := by
    unfold F24
    norm_num
  have hGp : 0 ≤ (1-p) * F24 p := mul_nonneg hq (F24_nonneg h0 hp1)
  have hA : 0 ≤ ε * (1-p)^25 := by positivity
  nlinarith

noncomputable def θ : ℝ := (1/2 - (1 - 82817/500000)^26) / (1 - 1/1000000000)

lemma θ_num : θ + 1/10000000 ≤ 1/2 - 1/250000 - (1 - 343343/2000000)^25 := by
  unfold θ
  norm_num

lemma θ_le_one : θ + 1/10000000 ≤ 1 := by
  unfold θ
  norm_num

lemma lower {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000) :
    log 2 - binEntropy ε * θ ≤ capacity (q ε) 30 5 := by
  have hh : 0 ≤ binEntropy ε := binEntropy_nonneg hε0.le (by linarith)
  set Y : ℝ → ℝ := fun p => (1-p)^26 + (1-ε) * M25 p with hY
  have hcont : ContinuousOn Y (Icc 0 (82817/500000)) := by
    apply Continuous.continuousOn
    simp only [hY, M25]
    fun_prop
  have hb : Y (82817/500000) ≤ 1/2 := by
    have hM : 0 ≤ M25 (82817/500000) := M25_nonneg (by norm_num) (by norm_num)
    have num : (1 - 82817/500000 : ℝ)^26 + M25 (82817/500000) ≤ 1/2 := by
      unfold M25
      norm_num
    simp only [hY]
    nlinarith
  have ha : (1/2 : ℝ) ≤ Y 0 := by
    simp only [hY, M25]
    norm_num
  obtain ⟨p0, hp0, hp0Y⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨hb, ha⟩
  have hp01 : p0 ≤ 1 := by linarith [hp0.2]
  have hM0 : 0 ≤ M25 p0 := M25_nonneg hp0.1 hp01
  have hpow : (1 - 82817/500000 : ℝ)^26 ≤ (1 - p0)^26 :=
    pow_le_pow_left₀ (by norm_num) (by linarith [hp0.2]) 26
  have hYe : (1-p0)^26 + (1-ε) * M25 p0 = 1/2 := hp0Y
  have hMθ : M25 p0 ≤ θ := by
    unfold θ
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hinfo : information (q ε) 30 5 p0 = log 2 - binEntropy ε * M25 p0 := by
    rw [info25, hYe]
    have : (1/2 : ℝ) = 2⁻¹ := by norm_num
    rw [this, binEntropy_two_inv]
  have hbdd : BddAbove (information (q ε) 30 5 '' Icc 0 1) := by
    refine ⟨log 2, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [info25]
    have := mul_nonneg hh (M25_nonneg hp.1 hp.2)
    linarith [binEntropy_le_log_two (p := (1-p)^26 + (1-ε) * M25 p)]
  have hle : information (q ε) 30 5 p0 ≤ capacity (q ε) 30 5 :=
    le_csSup hbdd ⟨p0, ⟨hp0.1, hp01⟩, rfl⟩
  have := mul_le_mul_of_nonneg_left hMθ hh
  linarith

lemma upper {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hc : binEntropy ε ≤ log 2 - binEntropy (1/2 + 1/250000)) :
    capacity (q ε) 30 6 ≤ log 2 - binEntropy ε * (θ + 1/10000000) := by
  have hh : 0 ≤ binEntropy ε := binEntropy_nonneg hε0.le (by linarith)
  unfold capacity
  apply csSup_le (Set.Nonempty.image _ ⟨0, Set.left_mem_Icc.2 zero_le_one⟩)
  rintro _ ⟨p, hp, rfl⟩
  rw [info24]
  have hM : 0 ≤ M24 p := M24_nonneg hp.1 hp.2
  have hq : 0 ≤ 1 - p := by linarith [hp.2]
  set y : ℝ := (1-p)^25 + (1-ε) * M24 p with hy
  have hy1 : y ≤ 1 := Y24_le_one hε0.le (by linarith) hp.1 hp.2
  have hy0 : 0 ≤ y := by
    have : 0 ≤ (1-ε) * M24 p := mul_nonneg (by linarith) hM
    have : 0 ≤ (1-p)^25 := by positivity
    linarith
  by_cases hclose : |y - 1/2| < 1/250000
  · have hpc : 343343/2000000 ≤ p := by
      by_contra hlt
      rw [not_le] at hlt
      have := Y24_low hε0.le hε1 hp.1 hlt.le
      rw [abs_lt] at hclose
      linarith [hclose.2]
    have hpow : (1 - p)^25 ≤ (1 - 343343/2000000 : ℝ)^25 :=
      pow_le_pow_left₀ hq (by linarith) 25
    have hMy : y - (1-p)^25 ≤ M24 p := by
      have : ε * M24 p ≥ 0 := mul_nonneg hε0.le hM
      simp only [hy]
      nlinarith
    rw [abs_lt] at hclose
    have hMθ : θ + 1/10000000 ≤ M24 p := by linarith [θ_num, hclose.1]
    have := mul_le_mul_of_nonneg_left hMθ hh
    linarith [binEntropy_le_log_two (p := y)]
  · have hbe : binEntropy y ≤ binEntropy (1/2 + 1/250000) := by
      rw [not_lt] at hclose
      rcases le_abs'.1 hclose with h | h
      · have h' : 1/2 + 1/250000 ≤ 1 - y := by linarith
        rw [← binEntropy_one_sub y]
        exact binEntropy_strictAntiOn.antitoneOn ⟨by norm_num, by norm_num⟩
          ⟨by linarith, by linarith⟩ h'
      · have h' : 1/2 + 1/250000 ≤ y := by linarith
        exact binEntropy_strictAntiOn.antitoneOn ⟨by norm_num, by norm_num⟩
          ⟨by linarith, hy1⟩ h'
    have h1 := mul_le_mul_of_nonneg_left θ_le_one hh
    have h2 := mul_nonneg hh hM
    linarith

end MO418877

open MO418877

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_418877.main) := by
  intro hmain
  have hcpos : 0 < log 2 - binEntropy (1/2 + 1/250000) := by
    have := binEntropy_lt_log_two.2 (show (1/2 + 1/250000 : ℝ) ≠ 2⁻¹ by norm_num)
    linarith
  have htend := binEntropy_continuous.tendsto 0
  rw [binEntropy_zero] at htend
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (htend.eventually (gt_mem_nhds hcpos))
  set ε : ℝ := min (r/2) (1/1000000000) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε ≤ 1/1000000000 := min_le_right _ _
  have hεr : ε ≤ r/2 := min_le_left _ _
  have hc : binEntropy ε ≤ log 2 - binEntropy (1/2 + 1/250000) := by
    have : dist ε 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
      linarith
    exact (hball this).le
  have hq : ∀ s, q ε s ∈ Icc (0 : ℝ) 1 := by
    intro s
    unfold q
    split_ifs <;> constructor <;> linarith
  have hanti : Antitone (q ε) := by
    intro a b hab
    unfold q
    split_ifs <;> first | linarith | omega
  have key := hmain (q ε) hq hanti 30 5 (by norm_num) (by norm_num)
  have hl := lower hε0 hε1
  have hu := upper hε0 hε1 hc
  have hpos : 0 < binEntropy ε := binEntropy_pos hε0 (by linarith)
  have : (5 : ℕ) + 1 = 6 := rfl
  rw [this] at key
  nlinarith
