import OMAStatements.S_oeis_a204214

open PowerSeries Finset OMA.S_oeis_a204214

private def endS (n x : ℕ) : Finset ℕ := (range (n + 1)).filter (fun y => |(y : ℤ) - x| ≤ n)

private def w (n x : ℕ) : ℕ := if x ≤ n then n + 1 else 2 * n + 1 - x

private def f (n x y : ℕ) : ℕ := if |(x : ℤ) - y| ≤ n then w n x * w n y else 0

private def toArr (t : Σ _ : ℕ × ℕ, ℕ × ℕ) (i : Fin 6) : ℕ :=
  if i.val = 1 then t.2.1 else if i.val = 2 then t.1.1
  else if i.val = 3 then t.1.2 else if i.val = 4 then t.2.2 else 0

private lemma a_sum (n : ℕ) : a n = ∑ x ∈ range (2 * n + 1), ∑ y ∈ range (2 * n + 1), f n x y := by
  let M := (range (2 * n + 1) ×ˢ range (2 * n + 1)).filter (fun p => |(p.1 : ℤ) - p.2| ≤ n)
  let T : Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) := M.sigma (fun p => endS n p.1 ×ˢ endS n p.2)
  have hinj : Function.Injective toArr := by
    rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩ h
    have := congrFun h 1; have := congrFun h 2; have := congrFun h 3; have := congrFun h 4
    simp_all [toArr]
  have heq : arrays n = (((T.image toArr : Finset (Fin 6 → ℕ)) : Set (Fin 6 → ℕ))) := by
    ext x; simp only [mem_coe, mem_image]; constructor
    · rintro ⟨hx0, hx5, hs⟩
      have d0 := hs 0 1 rfl; have d1 := hs 1 2 rfl; have d2 := hs 2 3 rfl
      have d3 := hs 3 4 rfl; have d4 := hs 4 5 rfl
      rw [abs_le] at d0 d1 d2 d3 d4
      refine ⟨⟨(x 2, x 3), (x 1, x 4)⟩, ?_, funext fun i => by fin_cases i <;> simp [toArr, hx0, hx5]⟩
      simp only [T, M, endS, mem_sigma, mem_filter, mem_product, mem_range, abs_le]; omega
    · rintro ⟨⟨⟨x2, x3⟩, ⟨x1, x4⟩⟩, ht, rfl⟩
      simp only [T, M, endS, mem_sigma, mem_filter, mem_product, mem_range, abs_le] at ht
      refine ⟨rfl, rfl, fun i j hij => ?_⟩
      fin_cases i <;> fin_cases j <;> simp [toArr, abs_le] at hij ⊢ <;> omega
  have hce : ∀ x ≤ 2 * n, (endS n x).card = w n x := fun x hx => by
    unfold w; split_ifs with h
    · rw [show endS n x = range (n + 1) from by
        ext y; simp only [endS, mem_filter, mem_range, abs_le, and_iff_left_iff_imp]; omega, card_range]
    · rw [show endS n x = Icc (x - n) n from by
        ext y; simp only [endS, mem_filter, mem_range, mem_Icc, abs_le]; omega, Nat.card_Icc]; omega
  rw [a, heq, Set.ncard_coe_finset, card_image_of_injective _ hinj, card_sigma]
  trans ∑ p ∈ M, w n p.1 * w n p.2
  · refine sum_congr rfl fun p hp => ?_
    simp only [M, mem_filter, mem_product, mem_range] at hp
    rw [card_product, hce _ (by omega), hce _ (by omega)]
  · rw [sum_filter, sum_product]; rfl

private lemma a_rat (n : ℕ) :
    (a n : ℚ) = (23 * (n : ℚ) ^ 4 + 74 * n ^ 3 + 91 * n ^ 2 + 52 * n + 12) / 12 := by
  have h1 : 2 * ∑ j ∈ range n, (j + 1) = n * (n + 1) := by
    induction n with | zero => simp | succ k ih => rw [sum_range_succ, mul_add, ih]; ring
  have h2 : 6 * ∑ j ∈ range n, (j + 1) ^ 2 = n * (n + 1) * (2 * n + 1) := by
    clear h1; induction n with | zero => simp | succ k ih => rw [sum_range_succ, mul_add, ih]; ring
  have hr : ∀ g : ℕ → ℕ, ∑ j ∈ range n, g (n - j) = ∑ j ∈ range n, g (j + 1) := fun g => by
    rw [← sum_range_reflect (fun j => g (j + 1)) n]
    exact sum_congr rfl fun j hj => by rw [mem_range] at hj; congr 1; omega
  have hAA : ∑ x ∈ range (n + 1), ∑ y ∈ range (n + 1), f n x y = (n + 1) ^ 4 := by
    trans ∑ _ ∈ range (n + 1), ∑ _ ∈ range (n + 1), (n + 1) * (n + 1)
    · refine sum_congr rfl fun x hx => sum_congr rfl fun y hy => ?_
      rw [mem_range] at hx hy; simp only [f, w, abs_le]
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    · simp; ring
  have hBB : ∑ j ∈ range n, ∑ k ∈ range n, f n (n + 1 + j) (n + 1 + k) =
      (∑ j ∈ range n, (j + 1)) ^ 2 := by
    trans ∑ j ∈ range n, (n - j) * ∑ k ∈ range n, (n - k)
    · refine sum_congr rfl fun j hj => ?_
      rw [mul_sum]; refine sum_congr rfl fun k hk => ?_
      rw [mem_range] at hj hk; simp only [f, w, abs_le]
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]; congr 1 <;> omega
    · rw [← sum_mul, hr (fun k => k), sq]
  have hBA : ∑ j ∈ range n, ∑ y ∈ range (n + 1), f n (n + 1 + j) y =
      ∑ x ∈ range (n + 1), ∑ j ∈ range n, f n x (n + 1 + j) := by
    rw [sum_comm]; refine sum_congr rfl fun x _ => sum_congr rfl fun j _ => ?_
    simp only [f]; rw [abs_sub_comm ((n + 1 + j : ℕ) : ℤ) x, mul_comm (w n _)]
  have hAB : ∑ x ∈ range (n + 1), ∑ j ∈ range n, f n x (n + 1 + j) =
      (n + 1) * ∑ j ∈ range n, (j + 1) ^ 2 := by
    rw [sum_comm]
    trans ∑ j ∈ range n, (n + 1) * (n - j) ^ 2
    · refine sum_congr rfl fun j hj => ?_
      rw [mem_range] at hj; conv_lhs => rw [show n + 1 = j + 1 + (n - j) by omega]
      rw [sum_range_add]
      rw [sum_eq_zero fun x hx => by rw [mem_range] at hx; simp only [f, abs_le]; rw [if_neg (by omega)],
        zero_add]
      trans ∑ _ ∈ range (n - j), (n + 1) * (n - j)
      · refine sum_congr rfl fun x hx => ?_
        rw [mem_range] at hx; simp only [f, w, abs_le]
        rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]; congr 1; omega
      · simp; ring
    · rw [← mul_sum, hr (· ^ 2)]
  have ha : a n = (n + 1) ^ 4 + 2 * ((n + 1) * ∑ j ∈ range n, (j + 1) ^ 2) +
      (∑ j ∈ range n, (j + 1)) ^ 2 := by
    rw [a_sum, show 2 * n + 1 = n + 1 + n by omega, sum_range_add]
    simp only [sum_range_add _ (n + 1) n, sum_add_distrib, hAA, hBA, hAB, hBB]; ring
  set S1 := ∑ j ∈ range n, (j + 1); set S2 := ∑ j ∈ range n, (j + 1) ^ 2
  have h12 : 12 * a n = 23 * n ^ 4 + 74 * n ^ 3 + 91 * n ^ 2 + 52 * n + 12 :=
    calc 12 * a n = 12 * (n + 1) ^ 4 + 4 * (n + 1) * (6 * S2) + 3 * (2 * S1) ^ 2 := by rw [ha]; ring
      _ = 12 * (n + 1) ^ 4 + 4 * (n + 1) * (n * (n + 1) * (2 * n + 1)) +
            3 * (n * (n + 1)) ^ 2 := by rw [h1, h2]
      _ = 23 * n ^ 4 + 74 * n ^ 3 + 91 * n ^ 2 + 52 * n + 12 := by ring
  have hq : (12 : ℚ) * a n = 23 * (n : ℚ) ^ 4 + 74 * n ^ 3 + 91 * n ^ 2 + 52 * n + 12 := by
    exact_mod_cast h12
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a204214.main := by
  refine ⟨?_, fun n hn => ?_⟩
  · set F : PowerSeries ℚ := mk fun n => if n = 0 then 0 else (a n : ℚ)
    rw [show F * (1 - X) ^ 5 = F - C 5 * (F * X ^ 1) + C 10 * (F * X ^ 2) - C 10 * (F * X ^ 3) +
        C 5 * (F * X ^ 4) - F * X ^ 5 by simp only [map_ofNat]; ring,
      show (X : PowerSeries ℚ) * (21 + 15 * X + 14 * X ^ 2 - 5 * X ^ 3 + X ^ 4) =
        C 21 * X ^ 1 + C 15 * X ^ 2 + C 14 * X ^ 3 - C 5 * X ^ 4 + X ^ 5 by
        simp only [map_ofNat]; ring]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, F, coeff_mk]
    match n with
    | 0 => norm_num
    | 1 | 2 | 3 | 4 | 5 => norm_num [a_rat]
    | m + 6 =>
      have h : ∀ k ≤ 5, k ≤ m + 6 ∧ m + 6 - k ≠ 0 := fun k hk => by omega
      simp only [h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
        show m + 6 ≠ 0 by omega, show m + 6 ≠ 5 by omega, ↓reduceIte, a_rat]
      simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
        show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
        show m + 6 - 5 = m + 1 by omega]
      push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    suffices (a (m + 5) : ℚ) =
        5 * a (m + 4) - 10 * a (m + 3) + 10 * a (m + 2) - 5 * a (m + 1) + a m by
      simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
        show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, Nat.add_sub_cancel]
      exact_mod_cast this
    simp only [a_rat]; push_cast; ring
