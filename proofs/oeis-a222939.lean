import OMAStatements.S_oeis_a222939

namespace OMA.S_oeis_a222939

open PowerSeries





/-- Number of columns of length m that pass the scan from the state (q, p, k). -/
def N (q : Option (Fin 5)) (p : Fin 5) (k m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 5, if ok q p k (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 5) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 5, f (List.ofFn x) =
      ∑ c : Fin 5, ∑ y : Fin m → Fin 5, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (q : Option (Fin 5)) (p : Fin 5) (k : ℕ) : N q p k 0 = 1 := by
  simp [N, ok]

theorem N_succ (q : Option (Fin 5)) (p : Fin 5) (k m : ℕ) :
    N q p k (m + 1) = ∑ c : Fin 5,
      if (decide (c.val ≤ k) && (q.all fun v => decide (c ≠ v))) = true then
        N (some p) c (max k (c.val + 1)) m else 0 := by
  have h := sum_cons m (fun l => if ok q p k l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : (decide (c.val ≤ k) && (q.all fun v => decide (c ≠ v))) = true
  · rw [if_pos hc]
    apply Finset.sum_congr rfl
    intro y _
    have hk : ok q p k (c :: List.ofFn y) = ok (some p) c (max k (c.val + 1)) (List.ofFn y) := by
      show ((decide (c.val ≤ k) && (q.all fun v => decide (c ≠ v))) && _) = _
      rw [hc, Bool.true_and]
    rw [hk]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro y _
    have hc' := Bool.eq_false_iff.mpr hc
    have hk : ok q p k (c :: List.ofFn y) = false := by
      show ((decide (c.val ≤ k) && (q.all fun v => decide (c ≠ v))) && _) = false
      rw [hc', Bool.false_and]
    simp [hk]

/-- Counts by class: g0 from (none, 0, 1), g1 from (some 0, 0, 1), g2 from (some q, p, 2) with
q, p < 2, g3 from (some q, p, 3) with q, p < 3, g4 from (some q, p, k) with k >= 4. -/
def st : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 1, 1, 1, 1)
  | m + 1 => ((st m).2.1 + (st m).2.2.1, (st m).2.2.1, (st m).2.2.1 + (st m).2.2.2.1,
      2 * (st m).2.2.2.1 + (st m).2.2.2.2, 4 * (st m).2.2.2.2)

theorem N_eq (m : ℕ) :
    N none 0 1 m = (st m).1 ∧ N (some 0) 0 1 m = (st m).2.1 ∧
      (∀ q p : Fin 5, q.val < 2 → p.val < 2 → N (some q) p 2 m = (st m).2.2.1) ∧
      (∀ q p : Fin 5, q.val < 3 → p.val < 3 → N (some q) p 3 m = (st m).2.2.2.1) ∧
      (∀ (q p : Fin 5) (k : ℕ), 4 ≤ k → N (some q) p k m = (st m).2.2.2.2) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, fun q p _ _ => ?_, fun q p _ _ => ?_, fun q p k _ => ?_⟩ <;> rw [N_zero] <;>
      rfl
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := ih
    refine ⟨?_, ?_, fun q p hq hp => ?_, fun q p hq hp => ?_, fun q p k hk => ?_⟩
    · rw [N_succ]
      simp [Fin.sum_univ_succ, h1, h2 0 1 (by decide) (by decide), st]
    · rw [N_succ]
      simp [Fin.sum_univ_succ, h2 0 1 (by decide) (by decide), st]
    · rw [N_succ]
      fin_cases q <;> fin_cases p <;> simp at hq hp ⊢ <;>
        simp [Fin.sum_univ_succ, h2 0 0 (by decide) (by decide), h2 0 1 (by decide) (by decide),
          h2 1 0 (by decide) (by decide), h2 1 1 (by decide) (by decide),
          h3 0 2 (by decide) (by decide), h3 1 2 (by decide) (by decide), st] <;> ring
    · rw [N_succ]
      fin_cases q <;> fin_cases p <;> simp at hq hp ⊢ <;>
        simp [Fin.sum_univ_succ, h3 0 0 (by decide) (by decide), h3 0 1 (by decide) (by decide),
          h3 0 2 (by decide) (by decide), h3 1 0 (by decide) (by decide),
          h3 1 1 (by decide) (by decide), h3 1 2 (by decide) (by decide),
          h3 2 0 (by decide) (by decide), h3 2 1 (by decide) (by decide),
          h3 2 2 (by decide) (by decide), h4 _ 3 4 (le_refl 4), st] <;> ring
    · rw [N_succ]
      have k1 : 0 < k := by omega
      have k2 : 1 < k := by omega
      have k3 : 2 < k := by omega
      have k4 : 3 < k := by omega
      have k5 : 4 ≤ k := hk
      fin_cases q <;>
        simp [Fin.sum_univ_succ, k1, k2, k3, k4, k5, h4 _ _ (max k _) (le_max_of_le_left hk),
          st] <;> ring

theorem a_succ (n : ℕ) : a (n + 1) = (st n).1 := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_succ]
  simp only [valid]
  simp
  rw [← (N_eq n).1, N, Finset.card_filter]

theorem g0_rec (m : ℕ) :
    ((st (m + 5)).1 : ℤ) = 7 * (st (m + 4)).1 - 14 * (st (m + 3)).1 + 8 * (st (m + 2)).1 := by
  simp only [st]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 4 + 1 by omega, show m + 6 - 2 = m + 3 + 1 by omega,
    show m + 6 - 3 = m + 2 + 1 by omega, show m + 6 = m + 5 + 1 by omega]
  simp only [a_succ]
  exact g0_rec m

theorem a_vals : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 7 ∧ a 5 = 20 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x(1 + x)(1 - 6x + 9x^2 - 3x^3)/((1 - x)(1 - 2x)(1 - 4x)), in Q[[x]]. -/
theorem gf_eq : gf = X * (1 + X) * (1 - 6 * X + 9 * X ^ 2 - 3 * X ^ 3) *
    ((1 - X) * (1 - 2 * X) * (1 - 4 * X))⁻¹ := by
  set D : ℚ⟦X⟧ := (1 - X) * (1 - 2 * X) * (1 - 4 * X) with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  obtain ⟨v1, v2, v3, v4, v5⟩ := a_vals
  have key : gf * D = X * (1 + X) * (1 - 6 * X + 9 * X ^ 2 - 3 * X ^ 3) := by
    have e : gf * D = gf - C 7 * (gf * X ^ 1) + C 14 * (gf * X ^ 2) - C 8 * (gf * X ^ 3) := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) * (1 + X) * (1 - 6 * X + 9 * X ^ 2 - 3 * X ^ 3) =
        X ^ 1 - C 5 * X ^ 2 + C 3 * X ^ 3 + C 6 * X ^ 4 - C 3 * X ^ 5 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3, v4, v5] <;> norm_num
    · have hr := recurrence n hn
      have hq : (a n : ℚ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show n ≠ 0 by omega,
        show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
        show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_false, show n ≠ 1 by omega,
        coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

theorem closed_int (m : ℕ) :
    ((st m).2.2.2.2 : ℤ) = 4 ^ m ∧ 2 * ((st m).2.2.2.1 : ℤ) = 4 ^ m + 2 ^ m ∧
      6 * ((st m).2.2.1 : ℤ) = 4 ^ m + 3 * 2 ^ m + 2 := by
  induction m with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> decide
  | succ m ih =>
    obtain ⟨h4, h3, h2⟩ := ih
    simp only [st]
    push_cast
    refine ⟨?_, ?_, ?_⟩
    · rw [h4]; ring
    · linear_combination 2 * h3 + 2 * h4
    · linear_combination h2 + 3 * h3

/-- Barker's closed form, for n > 2. -/
theorem closed_form (n : ℕ) (hn : 2 < n) :
    (a n : ℚ) = (256 + 9 * 2 ^ (3 + n) + 5 * 4 ^ n) / 384 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have ha : a (m + 3) = (st m).2.2.1 + (st (m + 1)).2.2.1 := by rw [a_succ]; rfl
  have h0 := (closed_int m).2.2
  have h1 := (closed_int (m + 1)).2.2
  have hq : 6 * (a (m + 3) : ℚ) = 5 * 4 ^ m + 9 * 2 ^ m + 4 := by
    rw [ha]
    have h0' : 6 * ((st m).2.2.1 : ℚ) = 4 ^ m + 3 * 2 ^ m + 2 := by exact_mod_cast h0
    have h1' : 6 * ((st (m + 1)).2.2.1 : ℚ) = 4 ^ (m + 1) + 3 * 2 ^ (m + 1) + 2 := by
      exact_mod_cast h1
    push_cast
    rw [pow_succ, pow_succ] at h1'
    linear_combination h0' + h1'
  rw [show 3 + (m + 3) = m + 6 by ring, pow_add, pow_add]
  linear_combination hq / 6

/-- Both of Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    gf = X * (1 + X) * (1 - 6 * X + 9 * X ^ 2 - 3 * X ^ 3) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X))⁻¹ ∧
    ∀ n : ℕ, 2 < n → (a n : ℚ) = (256 + 9 * 2 ^ (3 + n) + 5 * 4 ^ n) / 384 :=
  ⟨gf_eq, closed_form⟩

/-- Controls: a(1..14), the entry's data. -/
example : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 7 ∧ a 5 = 20 ∧ a 6 = 66 ∧ a 7 = 238 ∧
    a 8 = 902 ∧ a 9 = 3510 ∧ a 10 = 13846 ∧ a 11 = 54998 ∧ a 12 = 219222 ∧ a 13 = 875350 ∧
    a 14 = 3498326 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

set_option maxRecDepth 20000 in
/-- Control by direct enumeration of the 625 columns of length 4. -/
example : a 4 = 7 := by decide

end OMA.S_oeis_a222939

theorem OMA.solution : type_of% @OMA.S_oeis_a222939.main :=
  OMA.S_oeis_a222939.conjecture
