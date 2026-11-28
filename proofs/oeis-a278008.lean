import OMAStatements.S_oeis_a278008

namespace OMA.S_oeis_a278008

open PowerSeries






/-- The ways to add m rows below c (with p above c) and finish the scan. -/
def N (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) (m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 3 × Fin 3, if okRows p c (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 3 × Fin 3) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 3 × Fin 3, f (List.ofFn x) =
      ∑ c : Fin 3 × Fin 3, ∑ y : Fin m → Fin 3 × Fin 3, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 3 × Fin 3).sum_comp]
  rw [Fintype.sum_prod_type (f := fun q : (Fin 3 × Fin 3) × (Fin m → Fin 3 × Fin 3) =>
    f (List.ofFn ((Fin.consEquiv fun _ => Fin 3 × Fin 3) q)))]
  simp [List.ofFn_succ]

theorem N_zero (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) :
    N p c 0 = if rowOK p c none = true then 1 else 0 := by
  simp [N, okRows]

theorem N_succ (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) (m : ℕ) :
    N p c (m + 1) = ∑ r : Fin 3 × Fin 3, if rowOK p c (some r) = true then N (some c) r m else 0 := by
  have h := sum_cons m (fun l => if okRows p c l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : rowOK p c (some r) = true
  · rw [if_pos hr]
    apply Finset.sum_congr rfl
    intro y _
    simp only [okRows, hr, Bool.true_and]
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro y _
    have hr' := Bool.eq_false_iff.mpr hr
    have hk : okRows p c (r :: List.ofFn y) = false := by
      simp only [okRows, hr', Bool.false_and]
    simp [hk]

/-- The index of a state in the tables. -/
def idx (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) : ℕ :=
  (match p with
    | none => 0
    | some q => 1 + q.1.val * 3 + q.2.val) * 9 + c.1.val * 3 + c.2.val

/-- The table of N_1. -/
def t1 (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) : ℕ :=
  ([0, 3, 3, 3, 0, 3, 3, 3, 0, 0, 3, 3, 3, 0, 6, 3, 6, 3, 3, 3, 6, 3, 0, 6, 6, 6, 3, 0, 6, 3, 6, 3, 6, 3, 6, 3, 3, 3, 6, 3, 0, 6, 6, 6, 3, 3, 3, 6, 3, 0, 3, 6, 3, 0, 3, 6, 6, 6, 3, 3, 6, 3, 0, 0, 6, 3, 6, 3, 6, 3, 6, 3, 3, 6, 6, 6, 3, 3, 6, 3, 0, 0, 6, 3, 6, 3, 3, 3, 3, 0] : List ℕ).getD (idx p c) 0

/-- The table of N_2. -/
def t2 (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) : ℕ :=
  ([0, 15, 15, 15, 0, 15, 15, 15, 0, 0, 15, 15, 15, 0, 36, 15, 36, 27, 27, 15, 36, 15, 0, 36, 36, 36, 27, 0, 36, 15, 36, 27, 36, 15, 36, 27, 27, 15, 36, 15, 0, 36, 36, 36, 27, 27, 15, 36, 15, 0, 15, 36, 15, 0, 27, 36, 36, 36, 27, 15, 36, 15, 0, 0, 36, 15, 36, 27, 36, 15, 36, 27, 27, 36, 36, 36, 27, 15, 36, 15, 0, 0, 36, 15, 36, 27, 15, 15, 15, 0] : List ℕ).getD (idx p c) 0

/-- The table of N_3. -/
def t3 (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) : ℕ :=
  ([0, 99, 99, 99, 0, 99, 99, 99, 0, 0, 99, 99, 99, 0, 228, 99, 228, 159, 159, 99, 228, 99, 0, 228, 228, 228, 159, 0, 228, 99, 228, 159, 228, 99, 228, 159, 159, 99, 228, 99, 0, 228, 228, 228, 159, 159, 99, 228, 99, 0, 99, 228, 99, 0, 159, 228, 228, 228, 159, 99, 228, 99, 0, 0, 228, 99, 228, 159, 228, 99, 228, 159, 159, 228, 228, 228, 159, 99, 228, 99, 0, 0, 228, 99, 228, 159, 99, 99, 99, 0] : List ℕ).getD (idx p c) 0

lemma N1 (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) : N p c 1 = t1 p c := by
  rw [N_succ]
  simp only [N_zero]
  revert p c
  decide +kernel

lemma N2 (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) : N p c 2 = t2 p c := by
  rw [N_succ]
  simp only [N1]
  revert p c
  decide +kernel

lemma N3 (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) : N p c 3 = t3 p c := by
  rw [N_succ]
  simp only [N2]
  revert p c
  decide +kernel

/-- The recurrence of the continuation counts, on every state, from m = 1. -/
theorem N_rec (m : ℕ) : ∀ (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3),
    (N p c (m + 3) : ℤ) = 5 * N p c (m + 2) + 8 * N p c (m + 1) := by
  induction m with
  | zero =>
    intro p c
    rw [N3, N2, N1]
    revert p c
    decide +kernel
  | succ m ih =>
    intro p c
    rw [N_succ p c (m + 3), N_succ p c (m + 2), N_succ p c (m + 1)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    split_ifs
    · exact ih _ _
    · simp

theorem a_succ (n : ℕ) : a (n + 1) = ∑ c : Fin 3 × Fin 3, if c.1 = 0 then N none c n else 0 := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c.1 = 0
  · rw [if_pos hc]
    unfold N
    apply Finset.sum_congr rfl
    intro y _
    simp only [valid, hc, decide_true, Bool.true_and]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro y _
    simp [valid, hc]

/-- a(n) = 5 a(n-1) + 8 a(n-2), for n >= 4. -/
theorem a_rec (m : ℕ) : (a (m + 4) : ℤ) = 5 * a (m + 3) + 8 * a (m + 2) := by
  rw [a_succ (m + 3), a_succ (m + 2), a_succ (m + 1)]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs
  · exact N_rec m _ _
  · simp

lemma values : a 1 = 0 ∧ a 2 = 6 ∧ a 3 = 30 := by
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

/-- a(n) = 5 a(n-1) + 8 a(n-2), for n >= 3. -/
theorem recurrence (n : ℕ) (hn : 3 ≤ n) : (a n : ℤ) = 5 * a (n - 1) + 8 * a (n - 2) := by
  obtain ⟨v1, v2, v3⟩ := values
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · interval_cases n
    simp [v1, v2, v3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    exact a_rec m

/-- Barker's g.f., as A(x) (1 - 5x - 8x^2) = 6x^2 in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - 5 * X - 8 * X ^ 2) = 6 * X ^ 2 := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - 5 * X - 8 * X ^ 2) = A - C 5 * (A * X ^ 1) - C 8 * (A * X ^ 2) := by
    simp only [map_ofNat]; ring
  have e2 : (6 * X ^ 2 : ℤ⟦X⟧) = X ^ 2 * C 6 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 3 := ⟨n - 3, by omega⟩
    have h := recurrence (q + 3) (by omega)
    simp only [show q + 3 - 1 = q + 2 by omega, show q + 3 - 2 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 1 = 0 by omega,
      show 1 ≤ q + 3 by omega, show 2 ≤ q + 3 by omega, show ¬ q + 3 = 2 by omega, if_true, if_false]
    rw [h]
    ring

lemma zpow_eq (n : ℕ) : (2 : ℝ) ^ (-3 - (n : ℤ)) = 1 / 8 * (1 / 2) ^ n := by
  rw [show (-3 - (n : ℤ)) = -((n + 3 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, pow_add,
    mul_inv, one_div_pow]
  ring

/-- Barker's closed form, for n >= 1. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = 2 ^ (-3 - (n : ℤ)) *
    ((57 - 5 * Real.sqrt 57) * (5 + Real.sqrt 57) ^ n + (5 - Real.sqrt 57) ^ n * (57 + 5 * Real.sqrt 57)) / 19 := by
  have hs : Real.sqrt 57 ^ 2 = 57 := Real.sq_sqrt (by norm_num)
  obtain ⟨v1, v2, -⟩ := values
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [zpow_eq]
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · rw [v1]
        push_cast
        nlinarith [hs]
      · rw [v2]
        push_cast
        nlinarith [hs]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have h := recurrence (k + 3) (by omega)
      simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega] at h
      have h' : (a (k + 3) : ℝ) = 5 * a (k + 2) + 8 * a (k + 1) := by exact_mod_cast h
      rw [h', ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega), zpow_eq, zpow_eq]
      have r1 : (5 + Real.sqrt 57) ^ 2 = 10 * (5 + Real.sqrt 57) + 32 := by nlinarith [hs]
      have r2 : (5 - Real.sqrt 57) ^ 2 = 10 * (5 - Real.sqrt 57) + 32 := by nlinarith [hs]
      have e1 : (5 + Real.sqrt 57) ^ (k + 3) = (10 * (5 + Real.sqrt 57) + 32) * (5 + Real.sqrt 57) ^ (k + 1) := by
        rw [show k + 3 = (k + 1) + 2 by omega, pow_add, r1]
        ring
      have e2 : (5 + Real.sqrt 57) ^ (k + 2) = (5 + Real.sqrt 57) * (5 + Real.sqrt 57) ^ (k + 1) := by
        rw [pow_succ]; ring
      have e3 : (5 - Real.sqrt 57) ^ (k + 3) = (10 * (5 - Real.sqrt 57) + 32) * (5 - Real.sqrt 57) ^ (k + 1) := by
        rw [show k + 3 = (k + 1) + 2 by omega, pow_add, r2]
        ring
      have e4 : (5 - Real.sqrt 57) ^ (k + 2) = (5 - Real.sqrt 57) * (5 - Real.sqrt 57) ^ (k + 1) := by
        rw [pow_succ]; ring
      rw [e1, e2, e3, e4]
      ring

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - 5 * X - 8 * X ^ 2) = 6 * X ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 2 ^ (-3 - (n : ℤ)) *
      ((57 - 5 * Real.sqrt 57) * (5 + Real.sqrt 57) ^ n + (5 - Real.sqrt 57) ^ n * (57 + 5 * Real.sqrt 57)) / 19 :=
  ⟨gf, closed⟩

end OMA.S_oeis_a278008

theorem OMA.solution : type_of% @OMA.S_oeis_a278008.main :=
  OMA.S_oeis_a278008.conjecture
