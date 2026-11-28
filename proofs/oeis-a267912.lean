import OMAStatements.S_oeis_a267912

namespace OMA.S_oeis_a267912

open PowerSeries





/-- Number of rows of length m that pass the scan from the state (r, p, k). -/
def N (r : Option (Fin 3)) (p : Fin 3) (k m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 3, if ok r p k (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 3) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 3, f (List.ofFn x) =
      ∑ c : Fin 3, ∑ y : Fin m → Fin 3, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (r : Option (Fin 3)) (p : Fin 3) (k : ℕ) : N r p k 0 = 1 := by
  simp [N, ok]

theorem N_succ (r : Option (Fin 3)) (p : Fin 3) (k m : ℕ) :
    N r p k (m + 1) = ∑ c : Fin 3, if c.val ≤ k then (if c = p then
      (if (r.all fun v => decide (c ≠ v)) = true then N (some c) c k m else 0)
      else N r c (max k (c.val + 1)) m) else 0 := by
  have h := sum_cons m (fun l => if ok r p k l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hk : c.val ≤ k
  · rw [if_pos hk]
    by_cases hc : c = p
    · subst hc
      by_cases hr : (r.all fun v => decide (c ≠ v)) = true
      · rw [if_pos rfl, if_pos hr]
        apply Finset.sum_congr rfl
        intro y _
        have e : ok r c k (c :: List.ofFn y) = ok (some c) c k (List.ofFn y) := by
          show (decide (c.val ≤ k) && (if c = c then _ else _)) = _
          rw [if_pos rfl, hr, decide_eq_true hk, Bool.true_and, Bool.true_and]
        rw [e]
      · rw [if_pos rfl, if_neg hr]
        apply Finset.sum_eq_zero
        intro y _
        have e : ok r c k (c :: List.ofFn y) = false := by
          show (decide (c.val ≤ k) && (if c = c then _ else _)) = false
          rw [if_pos rfl, Bool.eq_false_iff.mpr hr, Bool.false_and, Bool.and_false]
        simp [e]
    · rw [if_neg hc]
      apply Finset.sum_congr rfl
      intro y _
      have e : ok r p k (c :: List.ofFn y) = ok r c (max k (c.val + 1)) (List.ofFn y) := by
        show (decide (c.val ≤ k) && (if c = p then _ else _)) = _
        rw [if_neg hc, decide_eq_true hk, Bool.true_and]
      rw [e]
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro y _
    have e : ok r p k (c :: List.ofFn y) = false := by
      show (decide (c.val ≤ k) && _) = false
      rw [decide_eq_false hk, Bool.false_and]
    simp [e]

/-- The counts by class, as a tuple (E, A, B, C, D): E from (none, 0, 1), A from (none, p, k)
with k >= 2, B from (some v, v, k) with k >= 2, C from (some v, p, k) with p ≠ v and k >= 2,
D from (some 0, 0, 1). -/
def st : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 1, 1, 1)
  | m + 1 => ((st m).2.2.2.2 + (st m).2.1, 2 * (st m).2.1 + (st m).2.2.1,
      2 * (st m).2.2.2.1, 2 * (st m).2.2.1 + (st m).2.2.2.1, (st m).2.2.2.1)

def E (m : ℕ) : ℕ := (st m).1
def A (m : ℕ) : ℕ := (st m).2.1
def B (m : ℕ) : ℕ := (st m).2.2.1
def Cc (m : ℕ) : ℕ := (st m).2.2.2.1
def D (m : ℕ) : ℕ := (st m).2.2.2.2

theorem E_succ (m : ℕ) : E (m + 1) = D m + A m := rfl
theorem A_succ (m : ℕ) : A (m + 1) = 2 * A m + B m := rfl
theorem B_succ (m : ℕ) : B (m + 1) = 2 * Cc m := rfl
theorem C_succ (m : ℕ) : Cc (m + 1) = 2 * B m + Cc m := rfl
theorem D_succ (m : ℕ) : D (m + 1) = Cc m := rfl

theorem N_eq (m : ℕ) :
    N none 0 1 m = E m ∧ (∀ p k, 2 ≤ k → N none p k m = A m) ∧
      (∀ v k, 2 ≤ k → N (some v) v k m = B m) ∧
      (∀ v p k, 2 ≤ k → p ≠ v → N (some v) p k m = Cc m) ∧ N (some 0) 0 1 m = D m := by
  induction m with
  | zero =>
    refine ⟨?_, fun p k _ => ?_, fun v k _ => ?_, fun v p k _ _ => ?_, ?_⟩ <;> rw [N_zero] <;> rfl
  | succ m ih =>
    obtain ⟨hE, hA, hB, hC, hD⟩ := ih
    refine ⟨?_, fun p k hk => ?_, fun v k hk => ?_, fun v p k hk hpv => ?_, ?_⟩
    · rw [N_succ, Fin.sum_univ_three, E_succ]
      simp [hD, hA 1 2 (le_refl 2)]
    · rw [N_succ, Fin.sum_univ_three, A_succ]
      have k0 : (0 : Fin 3).val ≤ k := by simp
      have k1 : (1 : Fin 3).val ≤ k := by simp; omega
      have k2 : (2 : Fin 3).val ≤ k := by simp; omega
      simp only [k0, k1, k2, if_true]
      fin_cases p <;>
        simp [hB _ k hk, hA _ (max k _) (le_max_of_le_left hk)] <;> ring
    · rw [N_succ, Fin.sum_univ_three, B_succ]
      have k0 : (0 : Fin 3).val ≤ k := by simp
      have k1 : (1 : Fin 3).val ≤ k := by simp; omega
      have k2 : (2 : Fin 3).val ≤ k := by simp; omega
      simp only [k0, k1, k2, if_true]
      fin_cases v <;>
        simp [hC _ _ (max k _) (le_max_of_le_left hk)] <;> ring
    · rw [N_succ, Fin.sum_univ_three, C_succ]
      have k0 : (0 : Fin 3).val ≤ k := by simp
      have k1 : (1 : Fin 3).val ≤ k := by simp; omega
      have k2 : (2 : Fin 3).val ≤ k := by simp; omega
      simp only [k0, k1, k2, if_true]
      fin_cases v <;> fin_cases p <;> simp at hpv ⊢ <;>
        simp [hB _ k hk, hB _ (max k _) (le_max_of_le_left hk),
          hC _ _ (max k _) (le_max_of_le_left hk)] <;> ring
    · rw [N_succ, Fin.sum_univ_three, D_succ]
      simp [hC 0 1 2 (le_refl 2) (by decide)]

theorem a_succ (n : ℕ) : a (n + 1) = E n := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_three]
  simp only [valid]
  simp
  rw [← (N_eq n).1, N, Finset.card_filter]

theorem E_rec (m : ℕ) :
    (E (m + 5) : ℤ) = 3 * E (m + 4) + 2 * E (m + 3) - 8 * E (m + 2) := by
  simp only [E, st]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 3 * a (n - 1) + 2 * a (n - 2) - 8 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 4 + 1 by omega, show m + 6 - 2 = m + 3 + 1 by omega,
    show m + 6 - 3 = m + 2 + 1 by omega, show m + 6 = m + 5 + 1 by omega]
  simp only [a_succ]
  exact E_rec m

theorem a_vals : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 4 ∧ a 4 = 11 ∧ a 5 = 29 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x(1 - x - 4x^2 + 3x^3 + 4x^4)/((1 - 2x)(1 - x - 4x^2)), in Q[[x]]. -/
theorem gf_eq : gf = X * (1 - X - 4 * X ^ 2 + 3 * X ^ 3 + 4 * X ^ 4) *
    ((1 - 2 * X) * (1 - X - 4 * X ^ 2))⁻¹ := by
  set Dn : ℚ⟦X⟧ := (1 - 2 * X) * (1 - X - 4 * X ^ 2) with hDn
  have hden : constantCoeff Dn ≠ 0 := by rw [hDn]; simp
  obtain ⟨v1, v2, v3, v4, v5⟩ := a_vals
  have key : gf * Dn = X * (1 - X - 4 * X ^ 2 + 3 * X ^ 3 + 4 * X ^ 4) := by
    have e : gf * Dn = gf - PowerSeries.C 3 * (gf * X ^ 1) - PowerSeries.C 2 * (gf * X ^ 2) +
        PowerSeries.C 8 * (gf * X ^ 3) := by
      rw [hDn]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) * (1 - X - 4 * X ^ 2 + 3 * X ^ 3 + 4 * X ^ 4) =
        X ^ 1 - X ^ 2 - PowerSeries.C 4 * X ^ 3 + PowerSeries.C 3 * X ^ 4 +
          PowerSeries.C 4 * X ^ 5 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3, v4, v5] <;> norm_num
    · have hr := recurrence n hn
      have hq : (a n : ℚ) = 3 * a (n - 1) + 2 * a (n - 2) - 8 * a (n - 3) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show n ≠ 0 by omega,
        show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
        show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_false, show n ≠ 1 by omega,
        show n ≠ 2 by omega, PowerSeries.coeff_C]
      linarith
  calc gf = gf * (Dn * Dn⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * Dn) * Dn⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- (1 + sqrt 17)^m = P(m) + Q(m) sqrt 17 and (1 - sqrt 17)^m = P(m) - Q(m) sqrt 17. -/
def pq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | m + 1 => ((pq m).1 + 17 * (pq m).2, (pq m).1 + (pq m).2)

theorem s17 : Real.sqrt 17 * Real.sqrt 17 = 17 := Real.mul_self_sqrt (by norm_num)

theorem pow_plus (m : ℕ) :
    (1 + Real.sqrt 17) ^ m = (pq m).1 + (pq m).2 * Real.sqrt 17 := by
  induction m with
  | zero => simp [pq]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [pq]
    push_cast
    linear_combination ((pq m).2 : ℝ) * s17

theorem pow_minus (m : ℕ) :
    (1 - Real.sqrt 17) ^ m = (pq m).1 - (pq m).2 * Real.sqrt 17 := by
  induction m with
  | zero => simp [pq]
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [pq]
    push_cast
    linear_combination ((pq m).2 : ℝ) * s17

/-- 2^(n + 5) a(n) = 10 P(n) + 38 Q(n) - 4^(n + 1) for n >= 3. -/
def G (n : ℕ) : ℤ := 10 * (pq n).1 + 38 * (pq n).2 - 4 ^ (n + 1)

theorem G_rec (m : ℕ) : G (m + 6) = 6 * G (m + 5) + 8 * G (m + 4) - 64 * G (m + 3) := by
  simp only [G, pq]
  ring

theorem closed_int (m : ℕ) :
    2 ^ (m + 8) * (a (m + 3) : ℤ) = G (m + 3) ∧ 2 ^ (m + 9) * (a (m + 4) : ℤ) = G (m + 4) ∧
      2 ^ (m + 10) * (a (m + 5) : ℤ) = G (m + 5) := by
  induction m with
  | zero =>
    obtain ⟨-, -, v3, v4, v5⟩ := a_vals
    simp only [zero_add, v3, v4, v5]
    refine ⟨?_, ?_, ?_⟩ <;> decide
  | succ m ih =>
    obtain ⟨h3, h4, h5⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [show m + 1 + 8 = m + 9 by ring, show m + 1 + 3 = m + 4 by ring]; exact h4
    · rw [show m + 1 + 9 = m + 10 by ring, show m + 1 + 4 = m + 5 by ring]; exact h5
    · rw [show m + 1 + 10 = m + 11 by ring, show m + 1 + 5 = m + 6 by ring]
      have hr := recurrence (m + 6) (by omega)
      rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
        show m + 6 - 3 = m + 3 by omega] at hr
      rw [hr, G_rec]
      linear_combination 6 * h5 + 8 * h4 - 64 * h3

/-- Barker's closed form, for n > 2. -/
theorem closed_form (n : ℕ) (hn : 2 < n) :
    (a n : ℝ) = 1 / 17 * 2 ^ (-5 - (n : ℤ)) * (-17 * 4 ^ (1 + n) +
      (85 - 19 * Real.sqrt 17) * (1 - Real.sqrt 17) ^ n +
      (1 + Real.sqrt 17) ^ n * (85 + 19 * Real.sqrt 17)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := (closed_int m).1
  unfold G at h
  have hA : 2 ^ (m + 8) * (a (m + 3) : ℝ) =
      10 * ((pq (m + 3)).1 : ℝ) + 38 * ((pq (m + 3)).2 : ℝ) - 4 ^ (m + 3 + 1) := by
    exact_mod_cast h
  have hz : (2 : ℝ) ^ (-5 - ((m + 3 : ℕ) : ℤ)) = 1 / 2 ^ (m + 8) := by
    rw [show (-5 - ((m + 3 : ℕ) : ℤ)) = -((m + 8 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, one_div]
  have hpos : (0 : ℝ) < 2 ^ (m + 8) := by positivity
  rw [hz, pow_plus, pow_minus, show 1 + (m + 3) = m + 3 + 1 by ring]
  field_simp
  linear_combination 17 * hA - (38 : ℝ) * ((pq (m + 3)).2 : ℝ) * s17

/-- Both of Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    gf = X * (1 - X - 4 * X ^ 2 + 3 * X ^ 3 + 4 * X ^ 4) *
      ((1 - 2 * X) * (1 - X - 4 * X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 2 < n → (a n : ℝ) = 1 / 17 * 2 ^ (-5 - (n : ℤ)) * (-17 * 4 ^ (1 + n) +
      (85 - 19 * Real.sqrt 17) * (1 - Real.sqrt 17) ^ n +
      (1 + Real.sqrt 17) ^ n * (85 + 19 * Real.sqrt 17)) :=
  ⟨gf_eq, closed_form⟩

/-- Controls: a(1..15), the entry's data. -/
example : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 4 ∧ a 4 = 11 ∧ a 5 = 29 ∧ a 6 = 77 ∧ a 7 = 201 ∧
    a 8 = 525 ∧ a 9 = 1361 ∧ a 10 = 3525 ∧ a 11 = 9097 ∧ a 12 = 23453 ∧ a 13 = 60353 ∧
    a 14 = 155189 ∧ a 15 = 398649 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

/-- Control by direct enumeration of the 81 rows of length 4. -/
example : a 4 = 11 := by decide

end OMA.S_oeis_a267912

theorem OMA.solution : type_of% @OMA.S_oeis_a267912.main :=
  OMA.S_oeis_a267912.conjecture
