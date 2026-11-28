import OMAStatements.S_mse_3290080

lemma R {a b : ℕ} (h : a ≤ b) (hb : 0 < b) : 100 * (b + 1) ^ a ≤ 272 * b ^ a := by
  have hb' : (0 : ℝ) < b := by positivity
  have : ((b : ℝ) + 1) ^ a ≤ Real.exp 1 * b ^ a := by
    calc ((b : ℝ) + 1) ^ a = (1 + 1 / b) ^ a * b ^ a := by rw [← mul_pow]; field_simp
      _ ≤ Real.exp (1 / b) ^ a * b ^ a := by gcongr; linarith [Real.add_one_le_exp (1 / (b : ℝ))]
      _ ≤ _ := by
        gcongr
        rw [← Real.exp_nat_mul, Real.exp_le_exp, mul_one_div, div_le_one hb']
        exact_mod_cast h
  have := Real.exp_one_lt_d9
  exact_mod_cast (by nlinarith [pow_pos hb' a] : (100 : ℝ) * ((b : ℝ) + 1) ^ a ≤ 272 * b ^ a)

lemma Q {a c : ℕ} (ha : 3 ≤ a) (h : a ≤ c) : c ^ a ≤ a ^ c := by
  induction c, h using Nat.le_induction with
  | base => rfl
  | succ c h ih =>
    rw [pow_succ]
    nlinarith [R h (by omega), Nat.mul_le_mul_left a ih, Nat.mul_le_mul_right (c ^ a) ha, Nat.zero_le (c ^ a)]

theorem OMA.solution : type_of% @OMA.S_mse_3290080.main := by
  intro a b ha hb hab
  refine ⟨fun e => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have T : ∀ n, 6 ≤ n → n ^ 2 + n + 2 < 2 ^ n := fun n hn => by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n _ ih => rw [pow_succ 2]; nlinarith
  rcases Nat.lt_or_ge a 3 with h | h
  · interval_cases a
    · simp at e; omega
    · rcases Nat.lt_or_ge b 6 with h | h
      · interval_cases b <;> simp_all
      · linarith [T b h]
  rcases Nat.lt_or_ge b 3 with h' | h'
  · interval_cases b
    · simp at e; omega
    · rcases Nat.lt_or_ge a 6 with h' | h'
      · interval_cases a <;> simp_all
      · linarith [T a h']
  rcases Nat.lt_or_gt_of_ne hab with h2 | h2
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    have : 9 ≤ c ^ 2 := by nlinarith
    have : 9 * c ≤ c ^ a := le_trans (by nlinarith) (Nat.pow_le_pow_right (by omega) h)
    rw [pow_succ] at e
    nlinarith [R (show a ≤ c by omega) (by omega), Nat.mul_le_mul_left a (Q h (show a ≤ c by omega)),
      Nat.mul_le_mul_right (c ^ a) h]
  · linarith [Q h' h2.le]
