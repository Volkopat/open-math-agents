import FormalConjectures.ErdosProblems.«657»

-- Shorter proof of Erdős Problem 657 — dim one upper
-- Credit: @B221393

open Real Filter Finset

theorem OMA.solution : type_of% @Erdos657.erdos_657.variants.dim_one_upper := by
  refine ⟨14, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop ⌈exp 16⌉₊] with n hn
  have hne : exp 16 ≤ n := Nat.ceil_le.1 hn
  have hnpos : (0 : ℝ) < n := (exp_pos _).trans_le hne
  have hlogn : 16 ≤ log n := by rw [← log_exp 16]; exact log_le_log (exp_pos _) hne
  set s := √(log n)
  have hs2 : s ^ 2 = log n := sq_sqrt (by linarith)
  have hs4 : 4 ≤ s := by
    simpa [show (16 : ℝ) = 4 ^ 2 by norm_num, sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)] using sqrt_le_sqrt hlogn
  set N := ⌈(n : ℝ) * exp (8 * s)⌉₊
  have hN1 : (n : ℝ) * exp (8 * s) ≤ N := Nat.le_ceil _
  have hM1 : (1 : ℝ) ≤ n * exp (8 * s) := one_le_mul_of_one_le_of_one_le
    ((one_le_exp (by norm_num)).trans hne) (one_le_exp (by linarith))
  have hNle : (N : ℝ) ≤ 2 * (n * exp (8 * s)) := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ n * exp (8 * s))
    linarith
  have hlogN : log N ≤ (s + 4) ^ 2 := by
    have h1 := log_le_log (by linarith) hNle
    rw [log_mul (by norm_num) (by positivity), log_mul hnpos.ne' (exp_pos _).ne', log_exp] at h1
    linarith [log_two_lt_d9, hs2]
  have hsqrt : √(log N) ≤ s + 4 :=
    (sqrt_le_sqrt hlogN).trans (by rw [sqrt_sq (by linarith)])
  have hroth : (n : ℝ) ≤ rothNumberNat N := by
    have h1 : (n : ℝ) ≤ n * exp (8 * s) * exp (-4 * (s + 4)) := by
      rw [mul_assoc, ← exp_add]
      exact le_mul_of_one_le_right hnpos.le (one_le_exp (by linarith))
    exact h1.trans ((mul_le_mul hN1 (exp_le_exp.2 (by linarith)) (by positivity) (by positivity)).trans
      Behrend.roth_lower_bound)
  obtain ⟨t, htN, htcard, htAP⟩ := rothNumberNat_spec N
  obtain ⟨u, hut, hucard⟩ := exists_subset_card_eq (by exact_mod_cast (htcard ▸ hroth) : n ≤ t.card)
  have key : ∀ a ∈ u, ∀ b ∈ u, ∀ c ∈ u, a ≠ c → a ≠ b → dist (a : ℝ) b ≠ dist (b : ℝ) c := by
    intro a ha b hb c hc hac hab h
    rw [Real.dist_eq, Real.dist_eq] at h
    rcases abs_eq_abs.1 h with h' | h'
    · exact hab (htAP (mem_coe.2 (hut ha)) (mem_coe.2 (hut hb)) (mem_coe.2 (hut hc))
        (by exact_mod_cast (by linarith : (a : ℝ) + c = b + b)))
    · exact hac (by exact_mod_cast (by linarith : (a : ℝ) = c))
  refine ⟨u.image (Nat.cast : ℕ → ℝ), by rw [card_image_of_injective _ Nat.cast_injective, hucard], ?_, ?_⟩
  · intro x hx y hy z hz hxy hyz hxz hiso
    simp only [coe_image, Set.mem_image, mem_coe] at hx hy hz
    obtain ⟨a, ha, rfl⟩ := hx; obtain ⟨b, hb, rfl⟩ := hy; obtain ⟨c, hc, rfl⟩ := hz
    have hab : a ≠ b := fun e => hxy (congrArg _ e)
    have hbc : b ≠ c := fun e => hyz (congrArg _ e)
    have hac : a ≠ c := fun e => hxz (congrArg _ e)
    rcases hiso with h | h | h
    · exact key a ha b hb c hc hac hab h
    · exact key b hb c hc a ha hab.symm hbc h
    · exact key c hc a ha b hb hbc.symm hac.symm h
  · have hsub : distanceSet (u.image (Nat.cast : ℕ → ℝ)) ⊆ (range N).image (Nat.cast : ℕ → ℝ) := by
      intro d hd
      simp only [distanceSet, mem_image, mem_offDiag] at hd
      obtain ⟨⟨_, _⟩, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, -⟩, rfl⟩ := hd
      have haN := mem_range.1 (htN (hut ha))
      have hbN := mem_range.1 (htN (hut hb))
      refine mem_image.2 ?_
      rcases le_total a b with h | h
      · exact ⟨b - a, mem_range.2 (by omega), by
          rw [Nat.cast_sub h, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 h))]⟩
      · exact ⟨a - b, mem_range.2 (by omega), by
          rw [Nat.cast_sub h, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 h))]⟩
    have hcard : (distinctDistances (u.image (Nat.cast : ℕ → ℝ)) : ℝ) ≤ N := by
      exact_mod_cast (card_le_card hsub).trans (card_image_le.trans (by simp))
    have hpow : 2 * exp (8 * s) ≤ (2 : ℝ) ^ (14 * s) := by
      rw [rpow_def_of_pos (by norm_num),
        show (2 : ℝ) * exp (8 * s) = exp (log 2 + 8 * s) by rw [exp_add, exp_log (by norm_num)]]
      exact exp_le_exp.2 (by nlinarith [log_two_gt_d9, log_two_lt_d9])
    calc _ ≤ (N : ℝ) := hcard
      _ ≤ n * (2 * exp (8 * s)) := by linarith
      _ ≤ n * (2 : ℝ) ^ (14 * s) := mul_le_mul_of_nonneg_left hpow hnpos.le
