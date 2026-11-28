import OMAStatements.S_oeis_a069623

-- Problem: A069623, the number of perfect powers <= n is O(sqrt n).
-- Credit: @bnb9001

namespace OMA_A069623_Proof

open Filter Asymptotics OMA.S_oeis_a069623

open Classical in
theorem subset_aux (n : ℕ) :
    (Finset.Icc 1 n).filter IsPerfectPower ⊆
      (Finset.range (Nat.sqrt n + 1)).image (fun b => b ^ 2) ∪
      (((Finset.range (n + 1)).filter (fun c => c ^ 3 ≤ n)) ×ˢ
        Finset.range (Nat.log 2 n + 1)).image (fun p => p.1 ^ p.2) := by
  classical
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨h1, hmn⟩, b, k, hk, rfl⟩ := hm
  rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · apply Finset.mem_union_left
    refine Finset.mem_image.mpr ⟨b ^ t, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      apply Nat.le_sqrt.mpr
      calc b ^ t * b ^ t = b ^ (t + t) := by rw [pow_add]
        _ ≤ n := hmn
    · rw [← pow_mul]; ring_nf
  · rcases Nat.lt_or_ge b 2 with hb | hb
    · interval_cases b
      · simp at h1
      · apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨1, ?_, by simp⟩
        rw [Finset.mem_range]
        have : 1 ≤ n := by simpa using hmn
        have : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
        omega
    · apply Finset.mem_union_right
      have ht : 1 ≤ t := by omega
      have hb3 : b ^ 3 ≤ b ^ (2 * t + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hbn : b ≤ b ^ (2 * t + 1) := Nat.le_self_pow (by omega) b
      refine Finset.mem_image.mpr ⟨(b, 2 * t + 1), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [Nat.lt_succ_iff]
      apply Nat.le_log_of_pow_le (by norm_num)
      calc 2 ^ (2 * t + 1) ≤ b ^ (2 * t + 1) := Nat.pow_le_pow_left hb _
        _ ≤ n := hmn

theorem cube_card (n : ℕ) :
    ((((Finset.range (n + 1)).filter (fun c => c ^ 3 ≤ n)).card : ℕ) : ℝ) ≤
      (n : ℝ) ^ ((1 : ℝ) / 3) + 1 := by
  classical
  have hsub : (Finset.range (n + 1)).filter (fun c => c ^ 3 ≤ n) ⊆
      Finset.range (⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 1) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_range] at hc
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    have h3 : ((c : ℝ) ^ (3 : ℕ)) ≤ n := by exact_mod_cast hc.2
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    calc (c : ℝ) = ((c : ℝ) ^ (3 : ℕ)) ^ (((3 : ℕ) : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast hc0 (by norm_num)).symm
      _ ≤ (n : ℝ) ^ (((3 : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) h3 (by norm_num)
      _ = (n : ℝ) ^ ((1 : ℝ) / 3) := by norm_num
  calc ((((Finset.range (n + 1)).filter (fun c => c ^ 3 ≤ n)).card : ℕ) : ℝ)
      ≤ ((Finset.range (⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1 := by simp
    _ ≤ (n : ℝ) ^ ((1 : ℝ) / 3) + 1 := by
        gcongr; exact Nat.floor_le (by positivity)

theorem log_bound (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.log n / Real.log 2 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ h2]
  have hp : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hp' : ((2 : ℝ) ^ (Nat.log 2 n)) ≤ n := by exact_mod_cast hp
  have := Real.log_le_log (by positivity) hp'
  rwa [Real.log_pow] at this

/-- the real majorant -/
noncomputable def g (x : ℝ) : ℝ :=
  Real.sqrt x + 1 + (x ^ ((1 : ℝ) / 3) + 1) * (Real.log x / Real.log 2 + 1)

open Classical in
theorem a_le_g (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) ≤ g n := by
  classical
  have hc := Finset.card_le_card (subset_aux n)
  have hu := Finset.card_union_le ((Finset.range (Nat.sqrt n + 1)).image (fun b => b ^ 2))
      ((((Finset.range (n + 1)).filter (fun c => c ^ 3 ≤ n)) ×ˢ
        Finset.range (Nat.log 2 n + 1)).image (fun p => p.1 ^ p.2))
  have hi1 := Finset.card_image_le (s := Finset.range (Nat.sqrt n + 1)) (f := fun b => b ^ 2)
  have hi2 := Finset.card_image_le (s := (((Finset.range (n + 1)).filter (fun c => c ^ 3 ≤ n)) ×ˢ
        Finset.range (Nat.log 2 n + 1))) (f := fun p => p.1 ^ p.2)
  rw [Finset.card_product, Finset.card_range] at hi2
  rw [Finset.card_range] at hi1
  have hnat : a n ≤ (Nat.sqrt n + 1) +
      ((Finset.range (n + 1)).filter (fun c => c ^ 3 ≤ n)).card * (Nat.log 2 n + 1) := by
    unfold a
    exact le_trans hc (le_trans hu (Nat.add_le_add hi1 hi2))
  have hreal : (a n : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) + 1 +
      ((((Finset.range (n + 1)).filter (fun c => c ^ 3 ≤ n)).card : ℕ) : ℝ) *
        (((Nat.log 2 n : ℕ) : ℝ) + 1) := by
    exact_mod_cast hnat
  have hs : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hcube := cube_card n
  have hlog := log_bound n hn
  unfold g
  calc (a n : ℝ) ≤ _ := hreal
    _ ≤ Real.sqrt n + 1 + ((n : ℝ) ^ ((1 : ℝ) / 3) + 1) *
          (Real.log n / Real.log 2 + 1) := by
        gcongr

theorem g_isBigO : g =O[atTop] fun x => Real.sqrt x := by
  have hev1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  -- constants are O of any function eventually ≥ 1
  have one_O : ∀ r : ℝ, 0 < r → (fun _ : ℝ => (1 : ℝ)) =O[atTop] fun x : ℝ => x ^ r := by
    intro r hr
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hev1] with x hx
    rw [norm_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.one_le_rpow hx hr.le
  have hA : (fun x : ℝ => x ^ ((1 : ℝ) / 3) + 1) =O[atTop] fun x : ℝ => x ^ ((1 : ℝ) / 3) :=
    (isBigO_refl _ _).add (one_O _ (by norm_num))
  have hlogO : (fun x : ℝ => Real.log x / Real.log 2) =O[atTop]
      fun x : ℝ => x ^ ((1 : ℝ) / 6) := by
    have := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 6) (by norm_num)).isBigO
    simpa [div_eq_mul_inv, mul_comm] using this.const_mul_left (Real.log 2)⁻¹
  have hB : (fun x : ℝ => Real.log x / Real.log 2 + 1) =O[atTop]
      fun x : ℝ => x ^ ((1 : ℝ) / 6) :=
    hlogO.add (one_O _ (by norm_num))
  have hAB := hA.mul hB
  have hsq : (fun x : ℝ => x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 6)) =ᶠ[atTop]
      fun x => Real.sqrt x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_add hx, Real.sqrt_eq_rpow]
    norm_num
  have hAB' := hAB.trans_eventuallyEq hsq
  have h1 : (fun _ : ℝ => (1 : ℝ)) =O[atTop] fun x : ℝ => Real.sqrt x := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hev1] with x hx
    rw [norm_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.one_le_sqrt.mpr hx
  have := ((isBigO_refl (fun x : ℝ => Real.sqrt x) atTop).add h1).add hAB'
  exact this

end OMA_A069623_Proof

open Filter Asymptotics OMA.S_oeis_a069623 OMA_A069623_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a069623.main := by
  have hg : (fun n : ℕ => g n) =O[atTop] (fun n : ℕ => Real.sqrt n) :=
    g_isBigO.comp_tendsto tendsto_natCast_atTop_atTop
  refine IsBigO.trans ?_ hg
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := a_le_g n hn
  have h0 : (0 : ℝ) ≤ a n := Nat.cast_nonneg _
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
    abs_of_nonneg (le_trans h0 h)]
  exact h
