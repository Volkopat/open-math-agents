import OMAStatements.S_oeis_a182614

namespace OMA.S_oeis_a182614

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

/-- A candidate m with m - 1 < n r^n <= m < (n + 1) r^n is the value. -/
lemma a_eq_of (n m : ℕ) (h1 : (n : ℝ) * Real.goldenRatio ^ n ≤ m)
    (h2 : (m : ℝ) < (n + 1) * Real.goldenRatio ^ n)
    (h3 : (m : ℝ) < (n : ℝ) * Real.goldenRatio ^ n + 1) : a n = m := by
  unfold a
  apply IsLeast.csInf_eq
  refine ⟨(mem_iff n m).2 ⟨h1, h2⟩, fun k hk => ?_⟩
  have hk1 := ((mem_iff n k).1 hk).1
  have : (m : ℝ) < k + 1 := by linarith
  have : m < k + 1 := by exact_mod_cast this
  omega

lemma t_pos : 0 < -Real.goldenConj := by linarith [Real.goldenConj_neg]

lemma t_lt : -Real.goldenConj < 5 / 8 := by
  have h5 : Real.sqrt 5 < 9 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  show -((1 - Real.sqrt 5) / 2) < 5 / 8
  linarith

lemma t_gt : 1 / 2 < -Real.goldenConj := by
  have h5 : 2 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  show 1 / 2 < -((1 - Real.sqrt 5) / 2)
  linarith

/-- n |psi|^n < 1 for n >= 1. -/
lemma small (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * (-Real.goldenConj) ^ n < 1 := by
  have ht := t_pos
  have ht2 := t_lt
  have ht3 := t_gt
  have hsq : (-Real.goldenConj) ^ 2 = 1 - (-Real.goldenConj) := by
    have := Real.goldenConj_sq
    nlinarith
  rcases (by omega : n = 1 ∨ 2 ≤ n) with h1 | h2
  · subst h1
    push_cast
    linarith
  · induction n, h2 using Nat.le_induction with
    | base =>
      rw [hsq]
      push_cast
      linarith
    | succ n h2n ih =>
      have hpow : 0 < (-Real.goldenConj) ^ n := pow_pos ht n
      have hstep : ((n : ℝ) + 1) * (-Real.goldenConj) ≤ (n : ℝ) := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast h2n
        nlinarith
      have : ((n + 1 : ℕ) : ℝ) * (-Real.goldenConj) ^ (n + 1) =
          ((n : ℝ) + 1) * (-Real.goldenConj) * (-Real.goldenConj) ^ n := by
        push_cast
        ring
      rw [this]
      calc ((n : ℝ) + 1) * (-Real.goldenConj) * (-Real.goldenConj) ^ n
          ≤ (n : ℝ) * (-Real.goldenConj) ^ n := by
            exact mul_le_mul_of_nonneg_right hstep hpow.le
        _ < 1 := ih (by omega)

lemma phi_pow_ge_one (n : ℕ) : 1 ≤ Real.goldenRatio ^ n :=
  one_le_pow₀ Real.one_lt_goldenRatio.le

/-- The closed form: a(n) = n L(n) + [n odd] for n >= 1. -/
lemma closed (n : ℕ) (hn : 1 ≤ n) :
    a n = if n % 2 = 0 then n * Ln n else n * Ln n + 1 := by
  have hs := small n hn
  have hL := Ln_cast n
  have hφ := phi_pow_ge_one n
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos (Nat.even_iff.mp he)]
    have heq : Real.goldenConj ^ n = (-Real.goldenConj) ^ n := by
      rw [neg_pow, he.neg_one_pow]; ring
    have h0 : 0 < (-Real.goldenConj) ^ n := pow_pos t_pos n
    have hcast : ((n * Ln n : ℕ) : ℝ) = (n : ℝ) * Ln n := by push_cast; ring
    apply a_eq_of
    · rw [hcast, hL]; nlinarith
    · rw [hcast, hL]; nlinarith
    · rw [hcast, hL]; nlinarith
  · rw [if_neg (by rw [Nat.odd_iff] at ho; omega)]
    have heq : Real.goldenConj ^ n = -((-Real.goldenConj) ^ n) := by
      rw [neg_pow, ho.neg_one_pow]; ring
    have h0 : 0 < (-Real.goldenConj) ^ n := pow_pos t_pos n
    have hcast : ((n * Ln n + 1 : ℕ) : ℝ) = (n : ℝ) * Ln n + 1 := by push_cast; ring
    apply a_eq_of
    · rw [hcast, hL]; nlinarith
    · rw [hcast, hL]; nlinarith
    · rw [hcast, hL]; nlinarith

/-- The closed form in Q, with the parity written through (-1)^n. -/
lemma closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (n : ℚ) * Ln n + (1 - (-1) ^ n) / 2 := by
  rw [closed n hn]
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos (Nat.even_iff.mp he), he.neg_one_pow]
    push_cast
    ring
  · rw [if_neg (by rw [Nat.odd_iff] at ho; omega), ho.neg_one_pow]
    push_cast
    ring

/-- The closed form satisfies the recurrence for every index. -/
lemma rec_closed (m : ℕ) :
    ((m + 6 : ℕ) : ℚ) * Ln (m + 6) + (1 - (-1) ^ (m + 6)) / 2 =
      2 * (((m + 5 : ℕ) : ℚ) * Ln (m + 5) + (1 - (-1) ^ (m + 5)) / 2) +
      2 * (((m + 4 : ℕ) : ℚ) * Ln (m + 4) + (1 - (-1) ^ (m + 4)) / 2) -
      4 * (((m + 3 : ℕ) : ℚ) * Ln (m + 3) + (1 - (-1) ^ (m + 3)) / 2) -
      2 * (((m + 2 : ℕ) : ℚ) * Ln (m + 2) + (1 - (-1) ^ (m + 2)) / 2) +
      2 * (((m + 1 : ℕ) : ℚ) * Ln (m + 1) + (1 - (-1) ^ (m + 1)) / 2) +
      (((m : ℕ) : ℚ) * Ln m + (1 - (-1) ^ m) / 2) := by
  have l2 : Ln (m + 2) = Ln (m + 1) + Ln m := rfl
  have l3 : Ln (m + 3) = Ln (m + 2) + Ln (m + 1) := rfl
  have l4 : Ln (m + 4) = Ln (m + 3) + Ln (m + 2) := rfl
  have l5 : Ln (m + 5) = Ln (m + 4) + Ln (m + 3) := rfl
  have l6 : Ln (m + 6) = Ln (m + 5) + Ln (m + 4) := rfl
  rw [l6, l5, l4, l3, l2]
  push_cast
  ring

/-- Wu's recurrence, for n > 6. -/
theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3) - 2 * a (n - 4) +
      2 * a (n - 5) + a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have hq : (a (m + 7) : ℚ) = 2 * a (m + 6) + 2 * a (m + 5) - 4 * a (m + 4) - 2 * a (m + 3) +
      2 * a (m + 2) + a (m + 1) := by
    rw [closedQ (m + 7) (by omega), closedQ (m + 6) (by omega), closedQ (m + 5) (by omega),
      closedQ (m + 4) (by omega), closedQ (m + 3) (by omega), closedQ (m + 2) (by omega),
      closedQ (m + 1) (by omega)]
    have := rec_closed (m + 1)
    simp only [show m + 1 + 6 = m + 7 by omega, show m + 1 + 5 = m + 6 by omega,
      show m + 1 + 4 = m + 5 by omega, show m + 1 + 3 = m + 4 by omega,
      show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at this
    linarith
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega]
  exact_mod_cast hq

lemma values : a 1 = 2 ∧ a 2 = 6 ∧ a 3 = 13 ∧ a 4 = 28 ∧ a 5 = 56 ∧ a 6 = 108 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [closed _ (by norm_num)] <;> decide

/-- Wu's generating function, as A(x) D(x) = N(x) in Z[[x]] (D has constant term -1). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
    ((X - 1) * (X + 1) * (X ^ 2 + X - 1) ^ 2) =
      X * (-2 * X ^ 4 + 2 * X ^ 3 + 3 * X ^ 2 - 2 * X - 2) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hA
  have e1 : A * ((X - 1) * (X + 1) * (X ^ 2 + X - 1) ^ 2) =
      A * X ^ 6 + C 2 * (A * X ^ 5) - C 2 * (A * X ^ 4) - C 4 * (A * X ^ 3) +
        C 2 * (A * X ^ 2) + C 2 * (A * X ^ 1) - A := by
    simp only [map_ofNat]
    ring
  have e2 : (X : ℤ⟦X⟧) * (-2 * X ^ 4 + 2 * X ^ 3 + 3 * X ^ 2 - 2 * X - 2) =
      -(X ^ 5 * C 2) + X ^ 4 * C 2 + X ^ 3 * C 3 - X ^ 2 * C 2 - X ^ 1 * C 2 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    hc]
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := values
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have h := recurrence (m + 7) (by omega)
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega] at h ⊢
    simp only [show ¬ m + 7 = 0 by omega, show ¬ m + 6 = 0 by omega, show ¬ m + 5 = 0 by omega,
      show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega, show ¬ m + 2 = 0 by omega,
      show ¬ m + 1 = 0 by omega, show 6 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega,
      show 4 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega,
      show 1 ≤ m + 7 by omega, show ¬ m + 7 = 5 by omega, show ¬ m + 7 = 4 by omega,
      show ¬ m + 7 = 3 by omega, show ¬ m + 7 = 2 by omega, show ¬ m + 7 = 1 by omega,
      if_true, if_false]
    rw [h]
    ring

/-- Both of Wu's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3) -
      2 * a (n - 4) + 2 * a (n - 5) + a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
      ((X - 1) * (X + 1) * (X ^ 2 + X - 1) ^ 2) =
        X * (-2 * X ^ 4 + 2 * X ^ 3 + 3 * X ^ 2 - 2 * X - 2) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a182614

theorem OMA.solution : type_of% @OMA.S_oeis_a182614.main :=
  OMA.S_oeis_a182614.conjecture
