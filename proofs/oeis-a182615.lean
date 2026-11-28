import OMAStatements.S_oeis_a182615

namespace OMA.S_oeis_a182615

open PowerSeries


/-- Lucas numbers. -/
def Ln : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | k + 2 => Ln (k + 1) + Ln k

lemma Ln_cast (k : ℕ) : (Ln k : ℝ) = Real.goldenRatio ^ k + Real.goldenConj ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · norm_num [Ln]
    · norm_num [Ln]
    · rw [Ln]
      push_cast
      rw [ih (k + 1) (by omega), ih k (by omega), pow_add Real.goldenRatio k 2,
        pow_add Real.goldenConj k 2, Real.goldenRatio_sq, Real.goldenConj_sq]
      ring

lemma r_eq : (1 + Real.sqrt 5) / 2 = Real.goldenRatio := rfl

/-- The defining set, as two inequalities. -/
lemma mem_iff (n k : ℕ) :
    ⌊(k : ℝ) / ((1 + Real.sqrt 5) / 2) ^ n⌋ = n ↔
      (n : ℝ) * Real.goldenRatio ^ n ≤ k ∧ (k : ℝ) < (n + 1) * Real.goldenRatio ^ n := by
  have hr : 0 < Real.goldenRatio ^ n := pow_pos Real.goldenRatio_pos n
  rw [r_eq, Int.floor_eq_iff, le_div_iff₀ hr, div_lt_iff₀ hr]
  push_cast
  rfl

/-- A candidate m with n r^n <= m < (n + 1) r^n < m + 1 is the value. -/
lemma a_eq_of (n m : ℕ) (h1 : (n : ℝ) * Real.goldenRatio ^ n ≤ m)
    (h2 : (m : ℝ) < (n + 1) * Real.goldenRatio ^ n)
    (h3 : ((n : ℝ) + 1) * Real.goldenRatio ^ n < m + 1) : a n = m := by
  unfold a
  apply IsGreatest.csSup_eq
  refine ⟨(mem_iff n m).2 ⟨h1, h2⟩, fun k hk => ?_⟩
  have hk2 := ((mem_iff n k).1 hk).2
  have : (k : ℝ) < m + 1 := lt_trans hk2 h3
  have : k < m + 1 := by exact_mod_cast this
  omega

lemma t_pos : 0 < -Real.goldenConj := by linarith [Real.goldenConj_neg]

lemma t_lt : -Real.goldenConj < 5 / 8 := by
  have h5 : Real.sqrt 5 < 9 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  show -((1 - Real.sqrt 5) / 2) < 5 / 8
  linarith

/-- (n + 1) |psi|^n < 1 for n >= 3. -/
lemma small (n : ℕ) (hn : 3 ≤ n) : ((n : ℝ) + 1) * (-Real.goldenConj) ^ n < 1 := by
  have ht := t_pos
  have ht2 := t_lt
  have hsq : (-Real.goldenConj) ^ 2 = 1 - (-Real.goldenConj) := by
    have := Real.goldenConj_sq
    nlinarith
  induction n, hn using Nat.le_induction with
  | base =>
    have h3 : (-Real.goldenConj) ^ 3 = 2 * (-Real.goldenConj) - 1 := by
      have : (-Real.goldenConj) ^ 3 = (-Real.goldenConj) * (-Real.goldenConj) ^ 2 := by ring
      rw [this, hsq]
      nlinarith [hsq]
    rw [h3]
    push_cast
    linarith
  | succ n hn ih =>
    have hpow : 0 < (-Real.goldenConj) ^ n := pow_pos ht n
    have hstep : ((n : ℝ) + 2) * (-Real.goldenConj) ≤ (n : ℝ) + 1 := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have : (((n + 1 : ℕ) : ℝ) + 1) * (-Real.goldenConj) ^ (n + 1) =
        ((n : ℝ) + 2) * (-Real.goldenConj) * (-Real.goldenConj) ^ n := by
      push_cast
      ring
    rw [this]
    calc ((n : ℝ) + 2) * (-Real.goldenConj) * (-Real.goldenConj) ^ n
        ≤ ((n : ℝ) + 1) * (-Real.goldenConj) ^ n := by
          exact mul_le_mul_of_nonneg_right hstep hpow.le
      _ < 1 := ih

lemma phi_pow_ge_one (n : ℕ) : 1 ≤ Real.goldenRatio ^ n :=
  one_le_pow₀ Real.one_lt_goldenRatio.le

/-- The closed form: a(n) = (n + 1) L(n) - [n even] for n >= 3. -/
lemma closed (n : ℕ) (hn : 3 ≤ n) :
    a n = if n % 2 = 0 then (n + 1) * Ln n - 1 else (n + 1) * Ln n := by
  have hs := small n hn
  have hL := Ln_cast n
  have hφ := phi_pow_ge_one n
  have hLpos : 1 ≤ Ln n := by
    have : (1 : ℝ) ≤ Ln n := by
      rw [hL]
      rcases Nat.even_or_odd n with he | ho
      · have := he.pow_pos (ne_of_lt Real.goldenConj_neg)
        linarith
      · have hneg : Real.goldenConj ^ n = -((-Real.goldenConj) ^ n) := by
          rw [neg_pow, ho.neg_one_pow]; ring
        have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        have : (-Real.goldenConj) ^ n < 1 := by
          have h0 : 0 < (-Real.goldenConj) ^ n := pow_pos t_pos n
          nlinarith
        -- phi^n >= phi^3 > 2 for n >= 3
        have hφ3 : 2 < Real.goldenRatio ^ n := by
          have h3 : Real.goldenRatio ^ 3 ≤ Real.goldenRatio ^ n :=
            pow_le_pow_right₀ Real.one_lt_goldenRatio.le hn
          have : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
            have := Real.goldenRatio_sq
            have e : Real.goldenRatio ^ 3 = Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
            rw [e, this]; nlinarith [this]
          linarith [Real.one_lt_goldenRatio]
        linarith
    exact_mod_cast this
  have hNpos : 1 ≤ (n + 1) * Ln n := by nlinarith
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos (Nat.even_iff.mp he)]
    have hpos : 0 < Real.goldenConj ^ n := he.pow_pos (ne_of_lt Real.goldenConj_neg)
    have heq : Real.goldenConj ^ n = (-Real.goldenConj) ^ n := by
      rw [neg_pow, he.neg_one_pow]; ring
    have hcast : (((n + 1) * Ln n - 1 : ℕ) : ℝ) = ((n : ℝ) + 1) * Ln n - 1 := by
      rw [Nat.cast_sub hNpos]; push_cast; ring
    apply a_eq_of
    · rw [hcast, hL]; nlinarith
    · rw [hcast, hL]; nlinarith
    · rw [hcast, hL]; nlinarith
  · rw [if_neg (by rw [Nat.odd_iff] at ho; omega)]
    have heq : Real.goldenConj ^ n = -((-Real.goldenConj) ^ n) := by
      rw [neg_pow, ho.neg_one_pow]; ring
    have h0 : 0 < (-Real.goldenConj) ^ n := pow_pos t_pos n
    have hcast : (((n + 1) * Ln n : ℕ) : ℝ) = ((n : ℝ) + 1) * Ln n := by push_cast; ring
    apply a_eq_of
    · rw [hcast, hL]; nlinarith
    · rw [hcast, hL]; nlinarith
    · rw [hcast, hL]; nlinarith

lemma a_one : a 1 = 3 := by
  have h5 : 2 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h5' : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  apply a_eq_of <;> simp only [pow_one, Real.goldenRatio] <;> push_cast <;> linarith

lemma a_two : a 2 = 7 := by
  have h5 : 2 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h5' : Real.sqrt 5 < 9 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hsq : Real.goldenRatio ^ 2 = (3 + Real.sqrt 5) / 2 := by
    rw [Real.goldenRatio_sq]; simp only [Real.goldenRatio]; ring
  apply a_eq_of <;> rw [hsq] <;> push_cast <;> linarith

/-- The closed form in Q, with the parity written through (-1)^n. -/
lemma closedQ (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = ((n : ℚ) + 1) * Ln n - (1 + (-1) ^ n) / 2 := by
  have hpos : 1 ≤ (n + 1) * Ln n := by
    have : 1 ≤ Ln n := by
      have h := closed n hn
      rcases Nat.lt_or_ge (Ln n) 1 with h0 | h0
      · have : Ln n = 0 := by omega
        have hL := Ln_cast n
        rw [this] at hL
        rcases Nat.even_or_odd n with he | ho
        · have := he.pow_pos (ne_of_lt Real.goldenConj_neg)
          have := pow_pos Real.goldenRatio_pos n
          push_cast at hL; linarith
        · have h1 := phi_pow_ge_one n
          have h2 : -1 < Real.goldenConj ^ n := by
            have : (-Real.goldenConj) ^ n < 1 :=
              pow_lt_one₀ t_pos.le (by linarith [Real.neg_one_lt_goldenConj]) (by omega)
            have heq : Real.goldenConj ^ n = -((-Real.goldenConj) ^ n) := by
              rw [neg_pow, ho.neg_one_pow]; ring
            linarith
          have h3 : 2 < Real.goldenRatio ^ n := by
            have h3 : Real.goldenRatio ^ 3 ≤ Real.goldenRatio ^ n :=
              pow_le_pow_right₀ Real.one_lt_goldenRatio.le hn
            have : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
              have := Real.goldenRatio_sq
              have e : Real.goldenRatio ^ 3 = Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
              rw [e, this]; nlinarith [this]
            linarith [Real.one_lt_goldenRatio]
          push_cast at hL; linarith
      · exact h0
    nlinarith
  rw [closed n hn]
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos (Nat.even_iff.mp he), he.neg_one_pow, Nat.cast_sub hpos]
    push_cast
    ring
  · rw [if_neg (by rw [Nat.odd_iff] at ho; omega), ho.neg_one_pow]
    push_cast
    ring

/-- The closed form satisfies the recurrence for every index. -/
lemma rec_closed (m : ℕ) :
    (((m + 6 : ℕ) : ℚ) + 1) * Ln (m + 6) - (1 + (-1) ^ (m + 6)) / 2 =
      2 * ((((m + 5 : ℕ) : ℚ) + 1) * Ln (m + 5) - (1 + (-1) ^ (m + 5)) / 2) +
      2 * ((((m + 4 : ℕ) : ℚ) + 1) * Ln (m + 4) - (1 + (-1) ^ (m + 4)) / 2) -
      4 * ((((m + 3 : ℕ) : ℚ) + 1) * Ln (m + 3) - (1 + (-1) ^ (m + 3)) / 2) -
      2 * ((((m + 2 : ℕ) : ℚ) + 1) * Ln (m + 2) - (1 + (-1) ^ (m + 2)) / 2) +
      2 * ((((m + 1 : ℕ) : ℚ) + 1) * Ln (m + 1) - (1 + (-1) ^ (m + 1)) / 2) +
      ((((m : ℕ) : ℚ) + 1) * Ln m - (1 + (-1) ^ m) / 2) := by
  have l2 : Ln (m + 2) = Ln (m + 1) + Ln m := rfl
  have l3 : Ln (m + 3) = Ln (m + 2) + Ln (m + 1) := rfl
  have l4 : Ln (m + 4) = Ln (m + 3) + Ln (m + 2) := rfl
  have l5 : Ln (m + 5) = Ln (m + 4) + Ln (m + 3) := rfl
  have l6 : Ln (m + 6) = Ln (m + 5) + Ln (m + 4) := rfl
  rw [l6, l5, l4, l3, l2]
  push_cast
  ring

/-- Wu's recurrence, for n > 8. -/
theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3) - 2 * a (n - 4) +
      2 * a (n - 5) + a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  have hq : (a (m + 9) : ℚ) = 2 * a (m + 8) + 2 * a (m + 7) - 4 * a (m + 6) - 2 * a (m + 5) +
      2 * a (m + 4) + a (m + 3) := by
    rw [closedQ (m + 9) (by omega), closedQ (m + 8) (by omega), closedQ (m + 7) (by omega),
      closedQ (m + 6) (by omega), closedQ (m + 5) (by omega), closedQ (m + 4) (by omega),
      closedQ (m + 3) (by omega)]
    have := rec_closed (m + 3)
    simp only [show m + 3 + 6 = m + 9 by omega, show m + 3 + 5 = m + 8 by omega,
      show m + 3 + 4 = m + 7 by omega, show m + 3 + 3 = m + 6 by omega,
      show m + 3 + 2 = m + 5 by omega, show m + 3 + 1 = m + 4 by omega] at this
    linarith
  rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
    show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega,
    show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega]
  exact_mod_cast hq

lemma values : a 1 = 3 ∧ a 2 = 7 ∧ a 3 = 16 ∧ a 4 = 34 ∧ a 5 = 66 ∧ a 6 = 125 ∧ a 7 = 232 ∧
    a 8 = 422 := by
  refine ⟨a_one, a_two, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [closed _ (by norm_num)] <;> decide

/-- Wu's generating function, as A(x) D(x) = N(x) in Z[[x]] (D has constant term -1). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
    ((X - 1) * (X + 1) * (X ^ 2 + X - 1) ^ 2) =
      X * (-X ^ 7 - X ^ 6 + 3 * X ^ 5 + 4 * X ^ 2 - X - 3) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hA
  have e1 : A * ((X - 1) * (X + 1) * (X ^ 2 + X - 1) ^ 2) =
      A * X ^ 6 + C 2 * (A * X ^ 5) - C 2 * (A * X ^ 4) - C 4 * (A * X ^ 3) +
        C 2 * (A * X ^ 2) + C 2 * (A * X ^ 1) - A := by
    simp only [map_ofNat]
    ring
  have e2 : (X : ℤ⟦X⟧) * (-X ^ 7 - X ^ 6 + 3 * X ^ 5 + 4 * X ^ 2 - X - 3) =
      -X ^ 8 - X ^ 7 + X ^ 6 * C 3 + X ^ 3 * C 4 - X ^ 2 - X ^ 1 * C 3 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    hc]
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := values
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have h := recurrence (m + 9) (by omega)
    simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
      show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega,
      show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega] at h ⊢
    simp only [show ¬ m + 9 = 0 by omega, show ¬ m + 8 = 0 by omega, show ¬ m + 7 = 0 by omega,
      show ¬ m + 6 = 0 by omega, show ¬ m + 5 = 0 by omega, show ¬ m + 4 = 0 by omega,
      show ¬ m + 3 = 0 by omega, show 6 ≤ m + 9 by omega, show 5 ≤ m + 9 by omega,
      show 4 ≤ m + 9 by omega, show 3 ≤ m + 9 by omega, show 2 ≤ m + 9 by omega,
      show 1 ≤ m + 9 by omega, show ¬ m + 9 = 8 by omega, show ¬ m + 9 = 7 by omega,
      show ¬ m + 9 = 6 by omega, show ¬ m + 9 = 3 by omega, show ¬ m + 9 = 2 by omega,
      show ¬ m + 9 = 1 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..8), and a(9) = 760, a(10) = 1352 from the closed form. -/
theorem controls : a 1 = 3 ∧ a 2 = 7 ∧ a 3 = 16 ∧ a 4 = 34 ∧ a 5 = 66 ∧ a 6 = 125 ∧
    a 7 = 232 ∧ a 8 = 422 ∧ a 9 = 760 ∧ a 10 = 1352 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := values
  refine ⟨v1, v2, v3, v4, v5, v6, v7, v8, ?_, ?_⟩ <;> rw [closed _ (by norm_num)] <;> decide

/-- Both of Wu's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3) -
      2 * a (n - 4) + 2 * a (n - 5) + a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
      ((X - 1) * (X + 1) * (X ^ 2 + X - 1) ^ 2) =
        X * (-X ^ 7 - X ^ 6 + 3 * X ^ 5 + 4 * X ^ 2 - X - 3) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a182615

theorem OMA.solution : type_of% @OMA.S_oeis_a182615.main :=
  OMA.S_oeis_a182615.conjecture
