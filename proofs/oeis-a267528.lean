import OMAStatements.S_oeis_a267528

namespace ProofA267528

open OMA.S_oeis_a267528
open PowerSeries

private def live : ℕ → ℤ → Prop
  | 0, i => i = 0
  | 1, i => i < -1 ∨ i = 0 ∨ 2 ≤ i
  | m + 2, i =>
    let n : ℤ := (m : ℤ) + 2
    i < -n ∨ 2 ≤ i ∨ (-n + 2 ≤ i ∧ i % 2 = 0)

private lemma rule141_table (l c r : Bool) :
    ruleOut l c r = true ↔
      ((¬l = true) ∧ (c = true ∨ (¬r = true))) ∨ (l = true ∧ c = true ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

private lemma cell_iff_live (n : ℕ) (i : ℤ) : cell n i = true ↔ live n i := by
  induction n generalizing i with
  | zero => simp [cell, live]
  | succ n ih =>
    rw [cell, rule141_table, ih, ih, ih]
    match n with
    | 0 => dsimp [live]; omega
    | 1 => change _ ↔ live (0 + 2) i; dsimp [live]; omega
    | m + 2 => change _ ↔ live ((m + 1) + 2) i; dsimp [live]; push_cast; omega

private lemma step_two (m : ℕ) : a (m + 4) = a (m + 2) + 3 := by
  let n := m + 2
  change a (n + 2) = a n + 3
  have ha_n : a n = ∑ r ∈ Finset.range (2 * n - 1),
      if cell n (((2 + r : ℕ) : ℤ) - n) then 1 else 0 := by
    unfold a
    rw [show 2 * n + 1 = 2 + (2 * n - 1) by dsimp [n]; omega, Finset.sum_range_add]
    have hpre : ∑ j ∈ Finset.range 2, (if cell n ((j : ℤ) - n) then (1 : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      have hj' := Finset.mem_range.mp hj
      have hf : ¬(cell n ((j : ℤ) - n) = true) := by
        rw [cell_iff_live]; change ¬live (m + 2) _; dsimp [live, n] at hj' ⊢; omega
      rw [if_neg hf]
    rw [hpre, zero_add]
  rw [ha_n]
  conv_lhs => unfold a
  rw [show 2 * (n + 2) + 1 = (4 + (2 * n - 1)) + 2 by dsimp [n]; omega,
      Finset.sum_range_add, Finset.sum_range_add]
  have hhead : ∑ j ∈ Finset.range 4,
      (if cell (n + 2) ((j : ℤ) - ((n + 2 : ℕ) : ℤ)) then (1 : ℤ) else 0) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have hf0 : ¬(cell (n + 2) (((0 : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = true) := by
      rw [cell_iff_live]; change ¬live ((m + 2) + 2) _; dsimp [live, n]; omega
    have hf1 : ¬(cell (n + 2) (((1 : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = true) := by
      rw [cell_iff_live]; change ¬live ((m + 2) + 2) _; dsimp [live, n]; omega
    rw [if_neg hf0, if_neg hf1, zero_add, zero_add]
    by_cases hm : m % 2 = 0
    · have ht2 : cell (n + 2) (((2 : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = true := by
        rw [cell_iff_live]; change live ((m + 2) + 2) _; dsimp [live, n]; omega
      have hf3 : ¬(cell (n + 2) (((3 : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = true) := by
        rw [cell_iff_live]; change ¬live ((m + 2) + 2) _; dsimp [live, n]; omega
      rw [if_pos ht2, if_neg hf3]; norm_num
    · have hf2 : ¬(cell (n + 2) (((2 : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = true) := by
        rw [cell_iff_live]; change ¬live ((m + 2) + 2) _; dsimp [live, n]; omega
      have ht3 : cell (n + 2) (((3 : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = true := by
        rw [cell_iff_live]; change live ((m + 2) + 2) _; dsimp [live, n]; omega
      rw [if_neg hf2, if_pos ht3]; norm_num
  have hmid : ∑ r ∈ Finset.range (2 * n - 1),
      (if cell (n + 2) (((4 + r : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) then (1 : ℤ) else 0) =
      ∑ r ∈ Finset.range (2 * n - 1),
      (if cell n (((2 + r : ℕ) : ℤ) - n) then 1 else 0) := by
    apply Finset.sum_congr rfl; intro r hr
    have hr' := Finset.mem_range.mp hr
    have heq : cell (n + 2) (((4 + r : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) =
        cell n (((2 + r : ℕ) : ℤ) - n) := by
      apply Bool.eq_iff_iff.mpr
      rw [cell_iff_live, cell_iff_live]
      change live ((m + 2) + 2) _ ↔ live (m + 2) _
      dsimp [live, n] at hr' ⊢; omega
    rw [heq]
  have htail : ∑ s ∈ Finset.range 2,
      (if cell (n + 2) ((((4 + (2 * n - 1) + s : ℕ) : ℤ)) - ((n + 2 : ℕ) : ℤ)) then (1 : ℤ) else 0) = 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have ht0 : cell (n + 2) ((((4 + (2 * n - 1) + 0 : ℕ) : ℤ)) - ((n + 2 : ℕ) : ℤ)) = true := by
      rw [cell_iff_live]; change live ((m + 2) + 2) _; dsimp [live, n]; omega
    have ht1 : cell (n + 2) ((((4 + (2 * n - 1) + 1 : ℕ) : ℤ)) - ((n + 2 : ℕ) : ℤ)) = true := by
      rw [cell_iff_live]; change live ((m + 2) + 2) _; dsimp [live, n]; omega
    rw [if_pos ht0, if_pos ht1]; norm_num
  rw [hhead, hmid, htail]; ring

private lemma a_phases (k : ℕ) :
    a (2 * k + 2) = 3 * (k : ℤ) + 2 ∧ a (2 * k + 3) = 3 * (k : ℤ) + 3 := by
  induction k with
  | zero =>
    have h2 : a 2 = 2 := by decide
    have h3 : a 3 = 3 := by decide
    simp [h2, h3]
  | succ k ih =>
    have he := step_two (2 * k)
    have ho := step_two (2 * k + 1)
    rw [show 2 * k + 4 = 2 * (k + 1) + 2 by omega, ih.1] at he
    rw [show 2 * k + 1 + 4 = 2 * (k + 1) + 3 by omega, show 2 * k + 1 + 2 = 2 * k + 3 by omega, ih.2] at ho
    exact ⟨by push_cast; linarith, by push_cast; linarith⟩

private lemma closed_int (n : ℕ) (hn : 1 < n) :
    4 * a n = 6 * (n : ℤ) - 5 + (-1 : ℤ) ^ n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, (a_phases m).1]
    have hp : (-1 : ℤ) ^ (2 * m + 2) = 1 := by
      rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]; norm_num
    rw [hp]; push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega, (a_phases m).2]
    have hp : (-1 : ℤ) ^ (2 * m + 3) = -1 := by
      rw [show 2 * m + 3 = 2 * (m + 1) + 1 by omega, pow_add, pow_mul]; norm_num
    rw [hp]; push_cast; ring

private lemma recurrence (n : ℕ) (hn : 4 < n) :
    a n = a (n - 1) + a (n - 2) - a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  have h1 := step_two (m + 1)
  have h0 := step_two m
  rw [show (m + 1) + 4 = m + 5 by omega, show (m + 1) + 2 = m + 3 by omega] at h1
  linarith

private abbrev p007494 (k : ℕ) : Prop := k % 3 = 0 ∨ k % 3 = 2

private lemma count_p007494 (k : ℕ) : Nat.count p007494 k = (2 * k + 1) / 3 := by
  induction k with
  | zero => simp [p007494]
  | succ k ih =>
    rw [Nat.count_succ, ih]
    dsimp [p007494]
    split_ifs <;> omega

private lemma nth_p007494_even (j : ℕ) : Nat.nth p007494 (2 * j) = 3 * j := by
  have hp : p007494 (3 * j) := by dsimp [p007494]; omega
  have hc : Nat.count p007494 (3 * j) = 2 * j := by rw [count_p007494]; omega
  simpa [hc] using Nat.nth_count hp

private lemma nth_p007494_odd (j : ℕ) : Nat.nth p007494 (2 * j + 1) = 3 * j + 2 := by
  have hp : p007494 (3 * j + 2) := by dsimp [p007494]; omega
  have hc : Nat.count p007494 (3 * j + 2) = 2 * j + 1 := by rw [count_p007494]; omega
  simpa [hc] using Nat.nth_count hp

private lemma eq_a007494 (n : ℕ) (hn : 4 < n) : a n = a007494 (n - 1) := by
  unfold a007494
  change a n = (Nat.nth p007494 (n - 1) : ℤ)
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
        show 2 * (j + 1) = 2 * j + 2 by omega, (a_phases j).1, nth_p007494_odd j]
    push_cast; ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) + 1 - 1 = 2 * (j + 1) by omega,
        show 2 * (j + 1) + 1 = 2 * j + 3 by omega, (a_phases j).2, nth_p007494_even (j + 1)]
    push_cast; ring

private lemma initials : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 5 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  simpa using (a_phases 1).1

private lemma generating :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X)) =
      1 + X ^ 3 + X ^ 4 := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have hprod : F * ((1 - X) ^ 2 * (1 + X)) =
      F - F * X ^ 1 - F * X ^ 2 + F * X ^ 3 := by ring
  have hrhs : (1 + X ^ 3 + X ^ 4 : PowerSeries ℚ) =
      1 + X ^ 3 * C 1 + X ^ 4 * C 1 := by
    simp only [map_one]; ring
  rw [hprod, hrhs]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_X_pow_mul', coeff_one, F, coeff_mk]
  obtain ⟨h0, h1, h2, h3, h4⟩ := initials
  rcases n with _ | _ | _ | _ | _ | m
  · simp [coeff_C, h0]
  · simp [coeff_C, h0, h1]; try norm_num
  · simp [coeff_C, h0, h1, h2]; try norm_num
  · simp [coeff_C, h0, h1, h2, h3]; try norm_num
  · simp [coeff_C, h1, h2, h3, h4]; try norm_num
  · simp only [show m + 1 + 1 + 1 + 1 + 1 = m + 5 by ring]
    have hr : (a (m + 5) : ℚ) = (a (m + 4) : ℚ) + (a (m + 3) : ℚ) - (a (m + 2) : ℚ) := by
      simpa [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
             show m + 5 - 3 = m + 2 by omega] using
        (show (a (m + 5) : ℚ) = (a (m + 5 - 1) : ℚ) + (a (m + 5 - 2) : ℚ) - (a (m + 5 - 3) : ℚ) from by
          exact_mod_cast recurrence (m + 5) (by omega))
    simp [coeff_C]
    linarith

private lemma real_hasSum_exp (y : ℝ) :
    HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

private lemma real_hasSum_mul_exp (x : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * x ^ n / (n.factorial : ℝ)) (x * Real.exp x) := by
  let f : ℕ → ℝ := fun n => (n : ℝ) * x ^ n / (n.factorial : ℝ)
  have hf1 : (fun m : ℕ => f (m + 1)) = fun m : ℕ => x * (x ^ m / (m.factorial : ℝ)) := by
    ext m
    dsimp [f]
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfac : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    field_simp [hm1, hfac]
    ring
  have hshift : HasSum (fun m : ℕ => f (m + 1)) (x * Real.exp x) := by
    rw [hf1]
    exact (real_hasSum_exp x).mul_left x
  simpa [f] using hshift.zero_add

private lemma egf_sum (x : ℝ) :
    HasSum (fun n : ℕ => (a n : ℝ) * x ^ n / (n.factorial : ℝ))
      (2 + x + (3 * x / 2 - 1) * Real.cosh x + 3 * (x - 1) * Real.sinh x / 2) := by
  have h_xe := (real_hasSum_mul_exp x).mul_left (3 / 2 : ℝ)
  have h_e1 := (real_hasSum_exp x).mul_left (-5 / 4 : ℝ)
  have h_em1 := (real_hasSum_exp (-x)).mul_left (1 / 4 : ℝ)
  have h_c0 : HasSum (fun n : ℕ => if n = 0 then (2 : ℝ) else 0) 2 := hasSum_ite_eq 0 2
  have h_c1 : HasSum (fun n : ℕ => if n = 1 then x else 0) x := hasSum_ite_eq 1 x
  have h_comb := ((((h_xe.add h_e1).add h_em1).add h_c0).add h_c1)
  obtain ⟨h0, h1, _, _, _⟩ := initials
  have hfun : (fun n : ℕ => (a n : ℝ) * x ^ n / (n.factorial : ℝ)) =
      fun n : ℕ =>
        (3 / 2 : ℝ) * ((n : ℝ) * x ^ n / (n.factorial : ℝ)) +
        (-5 / 4 : ℝ) * (x ^ n / (n.factorial : ℝ)) +
        (1 / 4 : ℝ) * ((-x) ^ n / (n.factorial : ℝ)) +
        (if n = 0 then (2 : ℝ) else 0) +
        (if n = 1 then x else 0) := by
    ext n
    rcases n with _ | _ | m
    · norm_num [h0]
    · norm_num [h1]; ring
    · have ha : (4 : ℝ) * (a (m + 2) : ℝ) =
          6 * ((m + 2 : ℕ) : ℝ) - 5 + (-1 : ℝ) ^ (m + 2) := by
        exact_mod_cast closed_int (m + 2) (by omega)
      have ha' : (a (m + 2) : ℝ) =
          (6 * ((m + 2 : ℕ) : ℝ) - 5 + (-1 : ℝ) ^ (m + 2)) / 4 := by
        linarith
      simp only [show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, if_false, add_zero]
      rw [ha', show (-x) ^ (m + 2) = (-1 : ℝ) ^ (m + 2) * x ^ (m + 2) by
            rw [← mul_pow]; ring_nf]
      ring
  have hval : (3 / 2 : ℝ) * (x * Real.exp x) + (-5 / 4 : ℝ) * Real.exp x +
        (1 / 4 : ℝ) * Real.exp (-x) + 2 + x =
      2 + x + (3 * x / 2 - 1) * Real.cosh x + 3 * (x - 1) * Real.sinh x / 2 := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  rw [hfun, ← hval]
  exact h_comb

end ProofA267528

theorem OMA.solution : type_of% @OMA.S_oeis_a267528.main :=
  ⟨ProofA267528.recurrence, ProofA267528.eq_a007494, ProofA267528.generating, ProofA267528.egf_sum⟩
