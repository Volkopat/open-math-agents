import OMAStatements.S_oeis_a081831

namespace A081831Proof

open Filter Topology
open OMA.S_oeis_a081831 (a aList)

private theorem prefix_length : ∀ n : ℕ, (aList n).length = n + 1
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => by
      rw [aList, List.length_append, prefix_length (n + 2)]
      rfl

private theorem prefix_step {n i : ℕ} (hi : i ≤ n) :
    (aList (n + 1)).getD i 0 = (aList n).getD i 0 := by
  rcases n with _ | _ | n
  · have : i = 0 := by omega
    subst i
    rfl
  · interval_cases i <;> rfl
  · have hlt : i < (aList (n + 2)).length := by
      rw [prefix_length]
      omega
    change (aList (n + 3)).getD i 0 = (aList (n + 2)).getD i 0
    rw [aList, List.getD_append _ _ _ _ hlt]

private theorem prefix_agrees {i n : ℕ} (hi : i ≤ n) :
    (aList n).getD i 0 = a i := by
  induction n with
  | zero =>
      have : i = 0 := by omega
      subst i
      rfl
  | succ n ih =>
      by_cases hn : i ≤ n
      · exact (prefix_step hn).trans (ih hn)
      · have : i = n + 1 := by omega
        subst i
        rfl

private theorem recurrence (n : ℕ) (h₁ : n + 3 - a (n + 2) ≤ n + 2)
    (h₂ : n + 3 - a (n + 1) ≤ n + 2)
    (h₃ : a (n + 3 - a (n + 2)) ≤ n + 2) :
    a (n + 3) = a (a (n + 3 - a (n + 2))) + a (n + 3 - a (n + 1)) := by
  change (aList (n + 3)).getD (n + 3) 0 = _
  have hlen : (aList (n + 2)).length = n + 3 := prefix_length _
  rw [aList, List.getD_append_right _ _ _ _ hlen.le, hlen, Nat.sub_self]
  change (aList (n + 2)).getD
    ((aList (n + 2)).getD (n + 3 - (aList (n + 2)).getD (n + 2) 0) 0) 0 +
    (aList (n + 2)).getD (n + 3 - (aList (n + 2)).getD (n + 1) 0) 0 = _
  rw [prefix_agrees (le_refl (n + 2)), prefix_agrees (Nat.le_succ (n + 1)),
    prefix_agrees h₁, prefix_agrees h₃, prefix_agrees h₂]

private noncomputable def ratio (g : ℕ → ℕ) (n : ℕ) : ℝ := (g n : ℝ) / (n : ℝ)

/-- A limit for a normalized sequence also controls its value at a rescaled index. -/
private theorem rescale {g k : ℕ → ℕ} {C K : ℝ} (hg₀ : g 0 = 0)
    (hg : Tendsto (ratio g) atTop (𝓝 C)) (hk : Tendsto (ratio k) atTop (𝓝 K)) :
    Tendsto (ratio (fun n => g (k n))) atTop (𝓝 (C * K)) := by
  have hmul (n : ℕ) : ratio (fun n => g (k n)) n = ratio g (k n) * ratio k n := by
    by_cases hkn : k n = 0
    · simp [ratio, hkn, hg₀]
    · unfold ratio
      exact (div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr hkn)).symm
  have hK : 0 ≤ K := le_of_tendsto_of_tendsto' tendsto_const_nhds hk (fun n => by
    unfold ratio
    positivity)
  rcases eq_or_lt_of_le hK with hK₀ | hKpos
  · subst K
    rw [mul_zero]
    obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hg).bddAbove
    have hupper : Tendsto (fun n => B * ratio k n) atTop (𝓝 0) := by
      simpa using hk.const_mul B
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper ?_ ?_
    · intro n
      unfold ratio
      positivity
    · intro n
      rw [hmul n]
      exact mul_le_mul_of_nonneg_right (hB ⟨k n, rfl⟩) (by unfold ratio; positivity)
  · have hkpos : ∀ᶠ n in atTop, K / 2 < ratio k n :=
      hk.eventually (lt_mem_nhds (by linarith : K / 2 < K))
    have hlow : Tendsto (fun n : ℕ => K / 2 * (n : ℝ)) atTop atTop :=
      Tendsto.pos_mul_atTop (by positivity) tendsto_const_nhds tendsto_natCast_atTop_atTop
    have hkTopR : Tendsto (fun n => (k n : ℝ)) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ hlow
      filter_upwards [hkpos, eventually_ne_atTop (0 : ℕ)] with n hn hn₀
      exact ((lt_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn₀)).mp hn).le
    have hkTop : Tendsto k atTop atTop := tendsto_natCast_atTop_iff.mp hkTopR
    exact ((hg.comp hkTop).mul hk).congr (fun n => (hmul n).symm)

private theorem shift_ratio (j : ℕ) : Tendsto (ratio (fun n => n - j)) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - (j : ℝ) / (n : ℝ)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop j, eventually_ne_atTop (0 : ℕ)] with n hn hn₀
  rw [ratio, Nat.cast_sub hn, sub_div, div_self (Nat.cast_ne_zero.mpr hn₀)]

private theorem shifted_a_ratio {C : ℝ} (h : Tendsto (ratio a) atTop (𝓝 C)) (j : ℕ) :
    Tendsto (ratio (fun n => a (n - j))) atTop (𝓝 C) := by
  simpa using rescale (g := a) (k := fun n => n - j) (show a 0 = 0 by rfl) h (shift_ratio j)

private theorem sub_ratio {C : ℝ} (h : Tendsto (ratio a) atTop (𝓝 C)) (j : ℕ) :
    Tendsto (ratio (fun n => n - a (n - j))) atTop (𝓝 (max (1 - C) 0)) := by
  have hlim : Tendsto (fun n => max (1 - ratio (fun n => a (n - j)) n) 0) atTop
      (𝓝 (max (1 - C) 0)) := (tendsto_const_nhds.sub (shifted_a_ratio h j)).max tendsto_const_nhds
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn₀
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn₀
  change max (1 - (a (n - j) : ℝ) / n) 0 = ((n - a (n - j) : ℕ) : ℝ) / n
  by_cases hle : a (n - j) ≤ n
  · have hreal : ((a (n - j) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
    rw [Nat.cast_sub hle, sub_div, div_self hn.ne', max_eq_left]
    exact sub_nonneg.mpr ((div_le_one₀ hn).mpr hreal)
  · have hreal : (n : ℝ) ≤ ((a (n - j) : ℕ) : ℝ) := by exact_mod_cast (le_of_not_ge hle)
    rw [Nat.sub_eq_zero_of_le (le_of_not_ge hle), Nat.cast_zero, zero_div, max_eq_right]
    exact sub_nonpos.mpr ((one_le_div₀ hn).mpr hreal)

private theorem shifted_a_pos {C : ℝ} (h : Tendsto (ratio a) atTop (𝓝 C))
    (hC : 0 < C) (j : ℕ) : ∀ᶠ n in atTop, 0 < a (n - j) := by
  filter_upwards [(shifted_a_ratio h j).eventually (lt_mem_nhds hC)] with n hn
  by_contra! hzero
  have ha : a (n - j) = 0 := by omega
  simp [ratio, ha] at hn

theorem no_positive_limit : ¬ ∃ C : ℝ, 0 < C ∧ Tendsto (ratio a) atTop (𝓝 C) := by
  rintro ⟨C, hC, h⟩
  let x : ℕ → ℕ := fun n => n - a (n - 1)
  let y : ℕ → ℕ := fun n => n - a (n - 2)
  let D : ℝ := max (1 - C) 0
  have ha₀ : a 0 = 0 := rfl
  have hx : Tendsto (ratio x) atTop (𝓝 D) := sub_ratio h 1
  have hy : Tendsto (ratio y) atTop (𝓝 D) := sub_ratio h 2
  have hax : Tendsto (ratio (fun n => a (x n))) atTop (𝓝 (C * D)) := rescale ha₀ h hx
  have CD_lt_one : C * D < 1 := by
    by_cases hC₁ : C ≤ 1
    · dsimp [D]
      rw [max_eq_left (sub_nonneg.mpr hC₁)]
      nlinarith [sq_nonneg (C - 1 / 2)]
    · have hC₁' : 1 ≤ C := le_of_not_ge hC₁
      simp [D, max_eq_right (sub_nonpos.mpr hC₁')]
  have hguard : ∀ᶠ n in atTop, a (x n) < n := by
    filter_upwards [hax.eventually (gt_mem_nhds CD_lt_one), eventually_ne_atTop (0 : ℕ)]
      with n hn hn₀
    have hpositive : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn₀
    have hlt := (div_lt_one₀ hpositive).mp hn
    exact_mod_cast hlt
  have hrec : ∀ᶠ n in atTop, a n = a (a (x n)) + a (y n) := by
    filter_upwards [eventually_ge_atTop 3, shifted_a_pos h hC 1, shifted_a_pos h hC 2, hguard]
      with m hm hm₁ hm₂ hm₃
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 3 := ⟨m - 3, by omega⟩
    have hsub₁ : n + 3 - 1 = n + 2 := by omega
    have hsub₂ : n + 3 - 2 = n + 1 := by omega
    simp only [hsub₁] at hm₁
    simp only [hsub₂] at hm₂
    simp only [x, hsub₁] at hm₃
    simpa only [x, y, hsub₁, hsub₂] using recurrence n (by omega) (by omega) (by omega)
  have hsum := (rescale ha₀ h hax).add (rescale ha₀ h hy)
  have hsame : Tendsto (ratio a) atTop (𝓝 (C * (C * D) + C * D)) := by
    refine hsum.congr' ?_
    filter_upwards [hrec] with n hn
    simp only [ratio, hn, Nat.cast_add, add_div]
  have hfix := tendsto_nhds_unique h hsame
  by_cases hC₁ : C ≤ 1
  · dsimp [D] at hfix
    rw [max_eq_left (sub_nonneg.mpr hC₁)] at hfix
    have hpositive : 0 < C ^ 3 := pow_pos hC _
    nlinarith
  · have hC₁' : 1 ≤ C := le_of_not_ge hC₁
    simp [D, max_eq_right (sub_nonpos.mpr hC₁')] at hfix
    linarith

end A081831Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a081831.main) := by
  exact A081831Proof.no_positive_limit
