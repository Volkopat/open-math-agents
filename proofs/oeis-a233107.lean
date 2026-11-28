import OMAStatements.S_oeis_a233107

namespace OMA.S_oeis_a233107

open PowerSeries





/-- The continuations by m rows of the scan from the state (pu, pv, s1, s2). -/
def N (pu pv : Fin 6) (s1 s2 : Bool) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 6 × Fin 6, if ok pu pv s1 s2 (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 6 × Fin 6) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 6 × Fin 6, f (List.ofFn x) =
      ∑ c : Fin 6 × Fin 6, ∑ y : Fin m → Fin 6 × Fin 6, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 6 × Fin 6).sum_comp]
  rw [Fintype.sum_prod_type (f := fun p : (Fin 6 × Fin 6) × (Fin m → Fin 6 × Fin 6) =>
    f (List.ofFn ((Fin.consEquiv fun _ => Fin 6 × Fin 6) p)))]
  simp [List.ofFn_succ]

theorem N_zero (pu pv : Fin 6) (s1 s2 : Bool) : N pu pv s1 s2 0 = 1 := by
  simp [N, ok]

/-- The condition on one row c below the row (pu, pv), without the rest of the scan. -/
def row (pu pv : Fin 6) (s1 s2 : Bool) (c : Fin 6 × Fin 6) : Bool :=
  decide (c.1.val + pu.val ≠ 5) && decide (c.2.val + pv.val ≠ 5) &&
    decide (c.1.val + c.2.val ≠ 5) && cellOk c.1 s1 s2 &&
    cellOk c.2 (s1 || decide (c.1.val = 1)) (s2 || decide (c.1.val = 2))

theorem N_succ (pu pv : Fin 6) (s1 s2 : Bool) (m : ℕ) :
    N pu pv s1 s2 (m + 1) = ∑ c : Fin 6 × Fin 6,
      if row pu pv s1 s2 c = true then
        N c.1 c.2 (s1 || decide (c.1.val = 1) || decide (c.2.val = 1))
          (s2 || decide (c.1.val = 2) || decide (c.2.val = 2)) m else 0 := by
  have h := sum_cons m (fun l => if ok pu pv s1 s2 l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : row pu pv s1 s2 c = true
  · rw [if_pos hc]
    apply Finset.sum_congr rfl
    intro y _
    simp only [row] at hc
    simp only [ok, hc, Bool.true_and]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro y _
    have hc' := Bool.eq_false_iff.mpr hc
    simp only [row] at hc'
    have hk : ok pu pv s1 s2 (c :: List.ofFn y) = false := by
      simp only [ok, hc', Bool.false_and]
    simp [hk]

/-- The index of a state in the tables. -/
def idx (pu pv : Fin 6) (s1 s2 : Bool) : ℕ :=
  ((pu.val * 6 + pv.val) * 2 + (if s1 then 1 else 0)) * 2 + (if s2 then 1 else 0)

/-- The table of N_1. -/
def t1 (pu pv : Fin 6) (s1 s2 : Bool) : ℕ :=
  ([5, 6, 14, 21, 6, 7, 14, 21, 6, 6, 17, 21, 5, 6, 13, 21, 4, 5, 14, 21, 4, 5, 13, 20, 6, 7, 14, 21, 8, 9, 14, 21, 8, 8, 17, 21, 7, 8, 13, 21, 5, 6, 13, 20, 6, 7, 14, 21, 6, 7, 17, 21, 8, 9, 17, 21, 8, 8, 21, 21, 7, 8, 16, 20, 5, 6, 17, 21, 6, 7, 17, 21, 6, 7, 13, 21, 8, 9, 13, 21, 8, 8, 16, 20, 7, 8, 12, 21, 5, 6, 13, 21, 6, 7, 13, 21, 3, 3, 14, 21, 4, 4, 13, 20, 4, 4, 17, 21, 4, 4, 13, 21, 2, 2, 14, 21, 3, 3, 14, 21, 4, 5, 13, 20, 6, 7, 14, 21, 6, 6, 17, 21, 5, 6, 13, 21, 4, 5, 14, 21, 5, 6, 14, 21] : List ℕ).getD (idx pu pv s1 s2) 0

/-- The table of N_2. -/
def t2 (pu pv : Fin 6) (s1 s2 : Bool) : ℕ :=
  ([68, 111, 245, 441, 82, 132, 245, 441, 82, 111, 294, 441, 61, 111, 210, 441, 54, 90, 245, 441, 63, 105, 231, 420, 82, 132, 245, 441, 101, 159, 245, 441, 101, 138, 294, 441, 80, 138, 210, 441, 59, 96, 231, 420, 82, 132, 245, 441, 82, 132, 294, 441, 101, 159, 294, 441, 101, 138, 357, 441, 80, 138, 252, 420, 59, 96, 294, 441, 82, 132, 294, 441, 82, 132, 210, 441, 101, 159, 210, 441, 101, 138, 252, 420, 80, 138, 168, 441, 59, 96, 210, 441, 82, 132, 210, 441, 33, 48, 245, 441, 38, 54, 231, 420, 38, 54, 294, 441, 38, 54, 210, 441, 10, 12, 245, 441, 33, 48, 245, 441, 63, 105, 231, 420, 82, 132, 245, 441, 82, 111, 294, 441, 61, 111, 210, 441, 54, 90, 245, 441, 68, 111, 245, 441] : List ℕ).getD (idx pu pv s1 s2) 0

/-- The table of N_3. -/
def t3 (pu pv : Fin 6) (s1 s2 : Bool) : ℕ :=
  ([1244, 2316, 4802, 9261, 1489, 2757, 4802, 9261, 1489, 2316, 5733, 9261, 1048, 2316, 3969, 9261, 999, 1875, 4802, 9261, 1176, 2205, 4557, 8820, 1489, 2757, 4802, 9261, 1802, 3309, 4802, 9261, 1802, 2868, 5733, 9261, 1361, 2868, 3969, 9261, 1067, 1986, 4557, 8820, 1489, 2757, 4802, 9261, 1489, 2757, 5733, 9261, 1802, 3309, 5733, 9261, 1802, 2868, 6909, 9261, 1361, 2868, 4704, 8820, 1067, 1986, 5733, 9261, 1489, 2757, 5733, 9261, 1489, 2757, 3969, 9261, 1802, 3309, 3969, 9261, 1802, 2868, 4704, 8820, 1361, 2868, 2940, 9261, 1067, 1986, 3969, 9261, 1489, 2757, 3969, 9261, 558, 993, 4802, 9261, 626, 1104, 4557, 8820, 626, 1104, 5733, 9261, 626, 1104, 3969, 9261, 136, 222, 4802, 9261, 558, 993, 4802, 9261, 1176, 2205, 4557, 8820, 1489, 2757, 4802, 9261, 1489, 2316, 5733, 9261, 1048, 2316, 3969, 9261, 999, 1875, 4802, 9261, 1244, 2316, 4802, 9261] : List ℕ).getD (idx pu pv s1 s2) 0

/-- The 43 states that a scan can reach after an admissible first row. -/
def reach (pu pv : Fin 6) (s1 s2 : Bool) : Bool :=
  ([true, false, true, true, false, false, true, true, false, false, false, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false, true, true, false, false, true, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, true, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, true, false, false, false, false, false, false, false, true, false, false, false, true, false, false, true, true, false, false, true, true, false, false, false, false, false, false, true, true, false, false, false, true, false, false, false, true, false, false, true, true, false, false, true, true] : List Bool).getD (idx pu pv s1 s2) false

/-- An admissible row leads from a reachable state to a reachable state. -/
lemma reach_step : ∀ (pu pv : Fin 6) (s1 s2 : Bool) (c : Fin 6 × Fin 6), reach pu pv s1 s2 = true →
    row pu pv s1 s2 c = true →
    reach c.1 c.2 (s1 || decide (c.1.val = 1) || decide (c.2.val = 1))
      (s2 || decide (c.1.val = 2) || decide (c.2.val = 2)) = true := by
  decide +kernel

lemma N1 (pu pv : Fin 6) (s1 s2 : Bool) : N pu pv s1 s2 1 = t1 pu pv s1 s2 := by
  rw [N_succ]
  simp only [N_zero]
  revert pu pv s1 s2
  decide +kernel

lemma N2 (pu pv : Fin 6) (s1 s2 : Bool) : N pu pv s1 s2 2 = t2 pu pv s1 s2 := by
  rw [N_succ]
  simp only [N1]
  revert pu pv s1 s2
  decide +kernel

lemma N3 (pu pv : Fin 6) (s1 s2 : Bool) : N pu pv s1 s2 3 = t3 pu pv s1 s2 := by
  rw [N_succ]
  simp only [N2]
  revert pu pv s1 s2
  decide +kernel

/-- The recurrence of the continuation counts, on every reachable state. -/
theorem N_rec (m : ℕ) : ∀ (pu pv : Fin 6) (s1 s2 : Bool), reach pu pv s1 s2 = true →
    (N pu pv s1 s2 (m + 3) : ℤ) =
      29 * N pu pv s1 s2 (m + 2) - 175 * N pu pv s1 s2 (m + 1) + 147 * N pu pv s1 s2 m := by
  induction m with
  | zero =>
    intro pu pv s1 s2 hr
    rw [N3, N2, N1, N_zero]
    revert pu pv s1 s2
    decide +kernel
  | succ m ih =>
    intro pu pv s1 s2 hr
    rw [N_succ pu pv s1 s2 (m + 3), N_succ pu pv s1 s2 (m + 2), N_succ pu pv s1 s2 (m + 1),
      N_succ pu pv s1 s2 m]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    split_ifs with hc
    · exact ih _ _ _ _ (reach_step pu pv s1 s2 c hr hc)
    · simp

/-- The first row, without the rest of the scan. -/
def first (c : Fin 6 × Fin 6) : Bool :=
  decide (c.1 = 0) && decide (c.1.val + c.2.val ≠ 5) && cellOk c.1 false false &&
    cellOk c.2 (decide (c.1.val = 1)) (decide (c.1.val = 2))

theorem a_succ (n : ℕ) : a (n + 1) = ∑ c : Fin 6 × Fin 6,
    if first c = true then
      N c.1 c.2 (decide (c.1.val = 1) || decide (c.2.val = 1))
        (decide (c.1.val = 2) || decide (c.2.val = 2)) n else 0 := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : first c = true
  · rw [if_pos hc]
    unfold N
    apply Finset.sum_congr rfl
    intro y _
    simp only [first] at hc
    simp only [valid, hc, Bool.true_and]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro y _
    have hc' := Bool.eq_false_iff.mpr hc
    simp only [first] at hc'
    have hk : valid (c :: List.ofFn y) = false := by
      simp only [valid, hc', Bool.false_and]
    simp [hk]

/-- An admissible first row leads to a reachable state. -/
lemma reach_first : ∀ c : Fin 6 × Fin 6, first c = true →
    reach c.1 c.2 (decide (c.1.val = 1) || decide (c.2.val = 1))
      (decide (c.1.val = 2) || decide (c.2.val = 2)) = true := by
  decide +kernel

/-- The recurrence of a, for n >= 4. -/
theorem a_rec (m : ℕ) : (a (m + 4) : ℤ) = 29 * a (m + 3) - 175 * a (m + 2) + 147 * a (m + 1) := by
  rw [a_succ (m + 3), a_succ (m + 2), a_succ (m + 1), a_succ m]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hc
  · exact N_rec m _ _ _ _ (reach_first c hc)
  · simp

lemma values : a 1 = 2 ∧ a 2 = 19 ∧ a 3 = 313 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [a_succ]
    simp only [N_zero]
    decide +kernel
  · rw [a_succ]
    simp only [N1]
    decide +kernel
  · rw [a_succ]
    simp only [N2]
    decide +kernel

/-- Barker's closed form, for n >= 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (105 + 18 * 7 ^ n + 5 * 21 ^ n) / 168 := by
  obtain ⟨v1, v2, v3⟩ := values
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · rw [v1]; norm_num
      · rw [v2]; norm_num
      · rw [v3]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h := a_rec m
      have h' : (a (m + 4) : ℚ) = 29 * a (m + 3) - 175 * a (m + 2) + 147 * a (m + 1) := by
        exact_mod_cast h
      rw [h', ih (m + 3) (by omega) (by omega), ih (m + 2) (by omega) (by omega),
        ih (m + 1) (by omega) (by omega)]
      ring

/-- Barker's g.f., as A(x) (1 - x)(1 - 7x)(1 - 21x) = x(2 - 7x)(1 - 16x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - X) * (1 - 7 * X) * (1 - 21 * X)) =
    X * (2 - 7 * X) * (1 - 16 * X) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * ((1 - X) * (1 - 7 * X) * (1 - 21 * X)) =
      A - C 29 * (A * X ^ 1) + C 175 * (A * X ^ 2) - C 147 * (A * X ^ 3) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (2 - 7 * X) * (1 - 16 * X) : ℤ⟦X⟧) = X ^ 1 * C 2 - X ^ 2 * C 39 + X ^ 3 * C 112 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h := a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega,
      show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega, show 1 ≤ m + 4 by omega,
      show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show ¬ m + 4 = 1 by omega,
      show ¬ m + 4 = 2 by omega, show ¬ m + 4 = 3 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..13). -/
theorem controls :
    a 1 = 2 ∧
    a 2 = 19 ∧
    a 3 = 313 ∧
    a 4 = 6046 ∧
    a 5 = 123352 ∧
    a 6 = 2565169 ∧
    a 7 = 53692063 ∧
    a 8 = 1126297996 ∧
    a 9 = 23643610702 ∧
    a 10 = 496455294319 ∧
    a 11 = 10425137467813 ∧
    a 12 = 218924920833946 ∧
    a 13 = 4597402575582052 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), closed _ (by norm_num)]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (105 + 18 * 7 ^ n + 5 * 21 ^ n) / 168) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - X) * (1 - 7 * X) * (1 - 21 * X)) =
      X * (2 - 7 * X) * (1 - 16 * X) :=
  ⟨closed, gf⟩

end OMA.S_oeis_a233107

theorem OMA.solution : type_of% @OMA.S_oeis_a233107.main :=
  OMA.S_oeis_a233107.conjecture
