import OMAReductions.R_Erdos186_erdos_186_variants_erdos_sarkozy_R1

open Finset Real

private lemma card_image_div_of_dvd {W : Finset ℕ} {r : ℕ} (hr : 0 < r) :
    ((W.filter (fun w => r ∣ w)).image (fun w => w / r)).card =
      (W.filter (fun w => r ∣ w)).card := by
  apply card_image_iff.mpr
  intro x hx y hy hxy
  have hdx : r ∣ x := (mem_filter.mp hx).2
  have hdy : r ∣ y := (mem_filter.mp hy).2
  have hx' : x = r * (x / r) := (Nat.mul_div_cancel' hdx).symm
  have hy' : y = r * (y / r) := (Nat.mul_div_cancel' hdy).symm
  dsimp at hxy
  rw [hx', hy', hxy]

theorem OMA.solution :
    OMA.R_Erdos186_erdos_186_variants_erdos_sarkozy_R1.H1 := by
  classical
  intro M U hUne hUM hdens
  let C : ℝ := 2000000 * (1 + Real.log (2 * (U.card : ℝ)))
  have hUpos : 0 < U.card := hUne.card_pos
  have hUR_pos : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast hUpos
  have h2U_ge : (2 : ℝ) ≤ 2 * (U.card : ℝ) := by
    have : (1 : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast hUpos
    linarith
  have hlog2U_pos : 0 < Real.log (2 * (U.card : ℝ)) :=
    Real.log_pos (by linarith)
  have hC_ge : (2000000 : ℝ) ≤ C := by
    dsimp [C]
    linarith
  have hC_pos : 0 < C := by linarith
  have hUM_card : U.card ≤ M := by
    have h := card_le_card hUM
    simpa [Nat.card_Icc] using h
  have hM_pos : 0 < M := lt_of_lt_of_le hUpos hUM_card
  have hM_le_U2 : (M : ℝ) ≤ (U.card : ℝ) ^ 2 := by
    have h1 : (M : ℝ) ≤ C * (M : ℝ) := by
      have : (1 : ℝ) ≤ C := by linarith
      nlinarith [Nat.cast_nonneg (α := ℝ) M]
    exact h1.trans hdens
  -- Main induction on L (strictly decreasing at each step)
  have hstep : ∀ L : ℕ, ∀ k d : ℕ, ∀ W : Finset ℕ,
      0 < d → 0 < L → W.Nonempty →
      d * L ≤ M → W.card ≤ U.card → 2 ^ k ≤ d →
      (U.card : ℝ) - (k : ℝ) * (42480 / C) * (U.card : ℝ) ≤ (W.card : ℝ) →
      W ⊆ Icc 1 L → (∀ w ∈ W, d * w ∈ U) →
      C * (L : ℝ) ≤ (W.card : ℝ) ^ 2 →
      ∃ d' L' : ℕ, ∃ W' : Finset ℕ, 0 < d' ∧ 0 < L' ∧ W'.Nonempty ∧
        d' * L' ≤ M ∧ d' * U.card ≤ 4 * M ∧ W'.card ≤ U.card ∧ U.card ≤ 2 * W'.card ∧
        W' ⊆ Icc 1 L' ∧ (∀ w ∈ W', d' * w ∈ U) ∧
        C * (L' : ℝ) ≤ (W'.card : ℝ) ^ 2 ∧
        ∀ r : ℕ, 1 < r → 42480 * (∑ w ∈ W', w) <
          (W'.filter fun w => ¬ r ∣ w).card * W'.card * W'.card := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro k d W hd hL hWne hdL hWU h2k hWlb hWL hWmem hWdens
      -- First prove k * (42480 / C) ≤ 1 / 2, so U.card ≤ 2 * W.card
      have hk_small : (k : ℝ) * (42480 / C) ≤ 1 / 2 := by
        have h2k_le_M : 2 ^ k ≤ M := h2k.trans (Nat.le_trans (Nat.le_mul_of_pos_right d hL) hdL)
        have h2k_le_U2 : ((2 : ℝ) ^ k) ≤ (U.card : ℝ) ^ 2 :=
          (by exact_mod_cast h2k_le_M : ((2 : ℝ) ^ k) ≤ (M : ℝ)).trans hM_le_U2
        have hlog_ineq : (k : ℝ) * Real.log 2 ≤ 2 * Real.log (2 * (U.card : ℝ)) := by
          have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((U.card : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) h2k_le_U2
          rw [Real.log_pow, Real.log_pow] at h1
          have h2 : Real.log (U.card : ℝ) ≤ Real.log (2 * (U.card : ℝ)) :=
            Real.log_le_log hUR_pos (by linarith)
          push_cast at h1
          linarith
        have hlog2_gt : (0.69 : ℝ) < Real.log 2 := by
          have := Real.log_two_gt_d9
          linarith
        have hk_le : (k : ℝ) ≤ 3 * (1 + Real.log (2 * (U.card : ℝ))) := by
          nlinarith [hlog_ineq, hlog2_gt, hlog2U_pos]
        have hfrac : (k : ℝ) * 42480 ≤ C / 2 := by
          dsimp [C]
          nlinarith [hk_le, hlog2U_pos]
        rw [mul_div_assoc', div_le_iff₀ hC_pos]
        linarith
      have hU_le_2W : U.card ≤ 2 * W.card := by
        have h1 : (U.card : ℝ) / 2 ≤ (W.card : ℝ) := by
          nlinarith [hWlb, hk_small, hUR_pos]
        exact_mod_cast (show (U.card : ℝ) ≤ 2 * (W.card : ℝ) by linarith)
      by_cases hgood : ∀ r : ℕ, 1 < r → 42480 * (∑ w ∈ W, w) <
          (W.filter fun w => ¬ r ∣ w).card * W.card * W.card
      · have hWL_card : W.card ≤ L := by
          have h := card_le_card hWL
          simpa [Nat.card_Icc] using h
        have hdU : d * U.card ≤ 4 * M := by
          calc d * U.card ≤ d * (2 * W.card) := Nat.mul_le_mul_left d hU_le_2W
            _ = 2 * (d * W.card) := by ring
            _ ≤ 2 * (d * L) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d hWL_card)
            _ ≤ 2 * M := Nat.mul_le_mul_left 2 hdL
            _ ≤ 4 * M := by omega
        exact ⟨d, L, W, hd, hL, hWne, hdL, hdU, hWU, hU_le_2W, hWL, hWmem, hWdens, hgood⟩
      · push_neg at hgood
        obtain ⟨r, hr1, hrbad⟩ := hgood
        have hr0 : 0 < r := by omega
        let B := W.filter (fun w => ¬ r ∣ w)
        let A := W.filter (fun w => r ∣ w)
        let W' := A.image (fun w => w / r)
        have hWpos : 0 < W.card := hWne.card_pos
        have hWR_pos : (0 : ℝ) < (W.card : ℝ) := by exact_mod_cast hWpos
        have hsum_le : ∑ w ∈ W, w ≤ W.card * L := by
          calc ∑ w ∈ W, w ≤ ∑ _w ∈ W, L := sum_le_sum fun w hw => (mem_Icc.mp (hWL hw)).2
            _ = W.card * L := by simp
        have hB_nat : B.card * W.card * W.card ≤ 42480 * (W.card * L) :=
          hrbad.trans (Nat.mul_le_mul_left 42480 hsum_le)
        have hB_real : (B.card : ℝ) * (W.card : ℝ) ^ 2 ≤ 42480 * (W.card : ℝ) * (L : ℝ) := by
          have h : ((B.card * W.card * W.card : ℕ) : ℝ) ≤ ((42480 * (W.card * L) : ℕ) : ℝ) :=
            Nat.cast_le.mpr hB_nat
          push_cast at h
          linarith
        have hL_le : (L : ℝ) ≤ (W.card : ℝ) ^ 2 / C := (le_div_iff₀ hC_pos).mpr (by linarith)
        have hB_le_W : (B.card : ℝ) ≤ (42480 / C) * (W.card : ℝ) := by
          have h1 : (B.card : ℝ) * (W.card : ℝ) ^ 2 ≤
              (42480 / C) * (W.card : ℝ) * (W.card : ℝ) ^ 2 := by
            have h2 : 42480 * (W.card : ℝ) * (L : ℝ) ≤
                42480 * (W.card : ℝ) * ((W.card : ℝ) ^ 2 / C) :=
              mul_le_mul_of_nonneg_left hL_le (by positivity)
            calc (B.card : ℝ) * (W.card : ℝ) ^ 2
                ≤ 42480 * (W.card : ℝ) * (L : ℝ) := hB_real
              _ ≤ 42480 * (W.card : ℝ) * ((W.card : ℝ) ^ 2 / C) := h2
              _ = (42480 / C) * (W.card : ℝ) * (W.card : ℝ) ^ 2 := by ring
          have hW2_pos : (0 : ℝ) < (W.card : ℝ) ^ 2 := sq_pos_of_pos hWR_pos
          exact le_of_mul_le_mul_right h1 hW2_pos
        have hB_le_U : (B.card : ℝ) ≤ (42480 / C) * (U.card : ℝ) :=
          hB_le_W.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hWU) (by positivity))
        have hAB_sum : A.card + B.card = W.card :=
          card_filter_add_card_filter_not (s := W) (p := fun w => r ∣ w)
        have hW'_card : W'.card = A.card := card_image_div_of_dvd hr0
        have hW'_eq : (W'.card : ℝ) = (W.card : ℝ) - (B.card : ℝ) := by
          have h : (W'.card : ℝ) + (B.card : ℝ) = (W.card : ℝ) := by
            rw [hW'_card]
            exact_mod_cast hAB_sum
          linarith
        have h42_le : (42480 / C : ℝ) ≤ 1 / 10 := by
          rw [div_le_div_iff₀ hC_pos (by norm_num)]
          linarith
        have hW'_ge_910 : (9 / 10 : ℝ) * (W.card : ℝ) ≤ (W'.card : ℝ) := by
          have : (B.card : ℝ) ≤ (1 / 10 : ℝ) * (W.card : ℝ) :=
            hB_le_W.trans (mul_le_mul_of_nonneg_right h42_le hWR_pos.le)
          linarith
        have hW'_ne : W'.Nonempty := by
          apply card_pos.mp
          have : (0 : ℝ) < (W'.card : ℝ) := by linarith
          exact_mod_cast this
        have hW'_sub : W' ⊆ Icc 1 (L / r) := by
          intro x hx
          obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
          have hwW : w ∈ W := (mem_filter.mp hw).1
          have hrdvd : r ∣ w := (mem_filter.mp hw).2
          have hw1 : 1 ≤ w := (mem_Icc.mp (hWL hwW)).1
          have hwL : w ≤ L := (mem_Icc.mp (hWL hwW)).2
          have hge1 : 1 ≤ w / r := by
            obtain ⟨q, hq⟩ := hrdvd
            have hqpos : 0 < q := by
              by_contra hq0
              have : q = 0 := by omega
              rw [this, mul_zero] at hq
              omega
            rw [hq, Nat.mul_div_cancel_left q hr0]
            exact hqpos
          exact mem_Icc.mpr ⟨hge1, Nat.div_le_div_right hwL⟩
        have hLr_pos : 0 < L / r := by
          obtain ⟨x, hx⟩ := hW'_ne
          have h1 := (mem_Icc.mp (hW'_sub hx)).1
          have h2 := (mem_Icc.mp (hW'_sub hx)).2
          omega
        have hLr_lt : L / r < L := Nat.div_lt_self hL hr1
        have hdr_pos : 0 < d * r := Nat.mul_pos hd hr0
        have hdr_Lr : (d * r) * (L / r) ≤ M := by
          calc (d * r) * (L / r) = d * (r * (L / r)) := by ring
            _ ≤ d * L := Nat.mul_le_mul_left d (Nat.mul_div_le L r)
            _ ≤ M := hdL
        have hW'_le_U : W'.card ≤ U.card := by
          have : W'.card ≤ W.card := by omega
          exact this.trans hWU
        have h2k1 : 2 ^ (k + 1) ≤ d * r := by
          rw [pow_succ]
          exact Nat.mul_le_mul h2k (by omega)
        have hW'_lb : (U.card : ℝ) - ((k + 1 : ℕ) : ℝ) * (42480 / C) * (U.card : ℝ) ≤ (W'.card : ℝ) := by
          push_cast
          linarith [hWlb, hB_le_U, hW'_eq]
        have hW'_mem : ∀ w ∈ W', (d * r) * w ∈ U := by
          intro x hx
          obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
          have hwW : w ∈ W := (mem_filter.mp hw).1
          have hrdvd : r ∣ w := (mem_filter.mp hw).2
          have hmul : (d * r) * (w / r) = d * w := by
            rw [mul_assoc, Nat.mul_div_cancel' hrdvd]
          rw [hmul]
          exact hWmem w hwW
        have hW'_dens : C * ((L / r : ℕ) : ℝ) ≤ (W'.card : ℝ) ^ 2 := by
          have hdiv_le : ((L / r : ℕ) : ℝ) ≤ (L : ℝ) / 2 := by
            have h1 : 2 * (L / r) ≤ r * (L / r) := Nat.mul_le_mul_right _ (by omega)
            have h2 : 2 * (L / r) ≤ L := h1.trans (Nat.mul_div_le L r)
            have h3 : (2 : ℝ) * ((L / r : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast h2
            linarith
          calc C * ((L / r : ℕ) : ℝ)
              ≤ C * ((L : ℝ) / 2) := mul_le_mul_of_nonneg_left hdiv_le hC_pos.le
            _ = (C * (L : ℝ)) / 2 := by ring
            _ ≤ (W.card : ℝ) ^ 2 / 2 := div_le_div_of_nonneg_right hWdens (by norm_num)
            _ ≤ ((9 / 10 : ℝ) * (W.card : ℝ)) ^ 2 := by nlinarith [sq_nonneg (W.card : ℝ)]
            _ ≤ (W'.card : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hW'_ge_910 2
        exact ih (L / r) hLr_lt (k + 1) (d * r) W' hdr_pos hLr_pos hW'_ne hdr_Lr
          hW'_le_U h2k1 hW'_lb hW'_sub hW'_mem hW'_dens
  exact hstep M 0 1 U Nat.one_pos hM_pos hUne (by simpa) le_rfl (by simp) (by simp) hUM
    (fun w hw => by simpa using hw) hdens
