import OMAStatements.S_oeis_a205342

-- Problem: A205342: Number of length 5 nonnegative integer arrays starting and ending with 0 with adjacent elements unequal but differing by no more than n.
-- Upstream: formal-conjectures statements/oeis-a205342.lean:0 (declaration OMA.S_oeis_a205342.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for the array (0, x, y, z, 0) the conditions on x and on z depend only on y, and
-- they are the same condition, so a(n) is the sum over y in 0..2n of c(y)^2, where c(y) is the
-- number of admissible x: c(0) = n, c(y) = n - 1 for 1 <= y <= n, c(y) = 2n + 1 - y for
-- n < y <= 2n. With 6 * (1^2 + ... + n^2) = n(n+1)(2n+1) this gives
-- 6a(n) + 3n^2 = 8n^3 + 7n; the recurrence is the vanishing fourth difference of this cubic,
-- and the g.f. follows by comparing coefficients.

open OMA.S_oeis_a205342 in
theorem OMA.solution : type_of% @OMA.S_oeis_a205342.main := by
  obtain ⟨cnt, hcnt⟩ : ∃ cnt : ℕ → ℕ → ℕ, ∀ n y, cnt n y =
      ((Finset.range (2 * n + 1)).filter (fun x => adj n 0 x ∧ adj n x y)).card :=
    ⟨_, fun _ _ => rfl⟩
  have hsum : ∀ n, a n = ∑ y ∈ Finset.range (2 * n + 1), cnt n y * cnt n y := by
    intro n
    simp only [hcnt]
    unfold a
    rw [Finset.card_filter]
    simp only [Finset.sum_product]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
    rw [ite_zero_mul_ite_zero, one_mul]
    refine if_congr ?_ rfl rfl
    simp only [adj]
    constructor
    · intro h
      omega
    · intro h
      omega
  have hlow0 : ∀ n, cnt n 0 = n := by
    intro n
    rw [hcnt]
    have e : (Finset.range (2 * n + 1)).filter (fun x => adj n 0 x ∧ adj n x 0) =
        Finset.Icc 1 n := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, adj]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [e]
    have h := Nat.card_Icc 1 n
    omega
  have hmid : ∀ n y, 1 ≤ y → y ≤ n → cnt n y = n - 1 := by
    intro n y hy1 hyn
    rw [hcnt]
    have e : (Finset.range (2 * n + 1)).filter (fun x => adj n 0 x ∧ adj n x y) =
        (Finset.Icc 1 n).erase y := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, Finset.mem_Icc, adj]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [e, Finset.card_erase_of_mem (Finset.mem_Icc.mpr ⟨hy1, hyn⟩)]
    have h := Nat.card_Icc 1 n
    omega
  have hhigh : ∀ n y, n < y → y ≤ 2 * n → cnt n y = 2 * n + 1 - y := by
    intro n y hy1 hy2
    rw [hcnt]
    have e : (Finset.range (2 * n + 1)).filter (fun x => adj n 0 x ∧ adj n x y) =
        Finset.Icc (y - n) n := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, adj]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [e]
    have h := Nat.card_Icc (y - n) n
    omega
  have hsq : ∀ N, 6 * ∑ j ∈ Finset.range N, (N - j) * (N - j) = N * (N + 1) * (2 * N + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ']
      have e : ∑ i ∈ Finset.range N, (N + 1 - (i + 1)) * (N + 1 - (i + 1)) =
          ∑ i ∈ Finset.range N, (N - i) * (N - i) :=
        Finset.sum_congr rfl (fun i _ => by rw [show N + 1 - (i + 1) = N - i by omega])
      rw [e, show N + 1 - 0 = N + 1 by omega, mul_add, ih]
      ring
  have hcf : ∀ n, 6 * a n + 3 * n ^ 2 = 8 * n ^ 3 + 7 * n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp [hsum 0, hlow0 0]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [hsum (k + 1), show 2 * (k + 1) + 1 = k + 1 + 1 + (k + 1) by ring,
        Finset.sum_range_add, Finset.sum_range_succ']
      have h1 : ∑ y ∈ Finset.range (k + 1), cnt (k + 1) (y + 1) * cnt (k + 1) (y + 1) =
          ∑ y ∈ Finset.range (k + 1), k * k := by
        refine Finset.sum_congr rfl (fun y hy => ?_)
        rw [Finset.mem_range] at hy
        rw [hmid (k + 1) (y + 1) (by omega) (by omega), Nat.add_sub_cancel]
      have h2 : ∑ x ∈ Finset.range (k + 1),
          cnt (k + 1) (k + 1 + 1 + x) * cnt (k + 1) (k + 1 + 1 + x) =
          ∑ x ∈ Finset.range (k + 1), (k + 1 - x) * (k + 1 - x) := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [Finset.mem_range] at hx
        rw [hhigh (k + 1) (k + 1 + 1 + x) (by omega) (by omega),
          show 2 * (k + 1) + 1 - (k + 1 + 1 + x) = k + 1 - x by omega]
      rw [h1, h2, Finset.sum_const, Finset.card_range, smul_eq_mul, hlow0 (k + 1)]
      obtain ⟨T, hT⟩ : ∃ T, T = ∑ x ∈ Finset.range (k + 1), (k + 1 - x) * (k + 1 - x) :=
        ⟨_, rfl⟩
      have h3 := hsq (k + 1)
      rw [← hT] at h3 ⊢
      linarith
  have hcfz : ∀ n, (6 : ℤ) * (a n : ℤ) + 3 * (n : ℤ) ^ 2 = 8 * (n : ℤ) ^ 3 + 7 * (n : ℤ) := by
    intro n
    exact_mod_cast hcf n
  have hcfq : ∀ n, (6 : ℚ) * (a n : ℚ) + 3 * (n : ℚ) ^ 2 = 8 * (n : ℚ) ^ 3 + 7 * (n : ℚ) := by
    intro n
    exact_mod_cast hcf n
  have a0 : a 0 = 0 := by
    have h := hcf 0
    norm_num at h
    omega
  have a1 : a 1 = 2 := by
    have h := hcf 1
    norm_num at h
    omega
  have a2 : a 2 = 11 := by
    have h := hcf 2
    norm_num at h
    omega
  have a3 : a 3 = 35 := by
    have h := hcf 3
    norm_num at h
    omega
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
    have h1 := hcfz (k + 1)
    have h2 := hcfz (k + 2)
    have h3 := hcfz (k + 3)
    have h4 := hcfz (k + 4)
    have h5 := hcfz (k + 5)
    push_cast at h1 h2 h3 h4 h5
    linarith
  · have e : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 4 =
        PowerSeries.mk (fun n => (a n : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
          + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6]
      ring
    have e2 : (PowerSeries.X * (2 + 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2) :
        PowerSeries ℚ) =
        PowerSeries.X ^ 1 + PowerSeries.X ^ 1 + PowerSeries.X ^ 2 + PowerSeries.X ^ 2 +
          PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + PowerSeries.X ^ 3 + PowerSeries.X ^ 3 := by
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m <;> norm_num [a0, a1, a2, a3]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
      rw [if_pos (show 1 ≤ j + 4 by omega), if_pos (show 2 ≤ j + 4 by omega),
        if_pos (show 3 ≤ j + 4 by omega), if_pos (show 4 ≤ j + 4 by omega),
        if_neg (show ¬ (j + 4 = 1) by omega), if_neg (show ¬ (j + 4 = 2) by omega),
        if_neg (show ¬ (j + 4 = 3) by omega),
        show j + 4 - 1 = j + 3 by omega, show j + 4 - 2 = j + 2 by omega,
        show j + 4 - 3 = j + 1 by omega, show j + 4 - 4 = j by omega]
      have h0 := hcfq j
      have h1 := hcfq (j + 1)
      have h2 := hcfq (j + 2)
      have h3 := hcfq (j + 3)
      have h4 := hcfq (j + 4)
      push_cast at h1 h2 h3 h4
      linarith
