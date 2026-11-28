import OMAStatements.S_oeis_a280399

namespace OMA.S_oeis_a280399

open PowerSeries







/-- Number of rows of length m that pass the scan from the state (q, p, k, e). -/
def N (q : Option (Fin 3)) (p : Fin 3) (k e m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 3, if ok q p k e (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 3) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 3, f (List.ofFn x) =
      ∑ c : Fin 3, ∑ y : Fin m → Fin 3, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (q : Option (Fin 3)) (p : Fin 3) (k e : ℕ) :
    N q p k e 0 = if e + lastBad q p = 1 then 1 else 0 := by
  by_cases h : e + lastBad q p = 1 <;> simp [N, ok, h]

theorem N_succ (q : Option (Fin 3)) (p : Fin 3) (k e m : ℕ) :
    N q p k e (m + 1) = ∑ c : Fin 3, if c.val ≤ k ∧ e + bad q p c ≤ 1 then
      N (some p) c (max k (c.val + 1)) (e + bad q p c) m else 0 := by
  have h := sum_cons m (fun l => if ok q p k e l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c.val ≤ k ∧ e + bad q p c ≤ 1
  · rw [if_pos hc]
    apply Finset.sum_congr rfl
    intro y _
    have e1 : ok q p k e (c :: List.ofFn y) =
        ok (some p) c (max k (c.val + 1)) (e + bad q p c) (List.ofFn y) := by
      show (decide (c.val ≤ k) && decide (e + bad q p c ≤ 1) && _) = _
      rw [decide_eq_true hc.1, decide_eq_true hc.2, Bool.true_and, Bool.true_and]
    rw [e1]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro y _
    have e1 : ok q p k e (c :: List.ofFn y) = false := by
      show (decide (c.val ≤ k) && decide (e + bad q p c ≤ 1) && _) = false
      by_cases h1 : c.val ≤ k
      · have h2 : ¬ (e + bad q p c ≤ 1) := fun h2 => hc ⟨h1, h2⟩
        rw [decide_eq_false h2, Bool.and_false, Bool.false_and]
      · rw [decide_eq_false h1, Bool.false_and, Bool.false_and]
    simp [e1]

/-- Counts by class: s0 from (none, 0, 1, 0), s7 from (some 0, 0, 1, 0), s9 and s10 from
(some v, v, k, e) with k >= 2 and e = 0, 1, s12 and s13 from (some q, p, k, e) with p ≠ q,
k >= 2 and e = 1, 0. -/
structure S where
  s0 : ℕ
  s7 : ℕ
  s9 : ℕ
  s10 : ℕ
  s12 : ℕ
  s13 : ℕ

def st : ℕ → S
  | 0 => ⟨0, 0, 0, 1, 0, 1⟩
  | m + 1 =>
    let s := st m
    ⟨s.s7 + s.s12, s.s7 + s.s13, s.s9 + 2 * s.s13, s.s10 + 2 * s.s12, s.s10, s.s9 + 2 * s.s12⟩

theorem s9_succ (m : ℕ) : (st (m + 1)).s9 = (st m).s9 + 2 * (st m).s13 := rfl
theorem s10_succ (m : ℕ) : (st (m + 1)).s10 = (st m).s10 + 2 * (st m).s12 := rfl
theorem s12_succ (m : ℕ) : (st (m + 1)).s12 = (st m).s10 := rfl
theorem s13_succ (m : ℕ) : (st (m + 1)).s13 = (st m).s9 + 2 * (st m).s12 := rfl

theorem N_eq (m : ℕ) :
    N none 0 1 0 m = (st m).s0 ∧ N (some 0) 0 1 0 m = (st m).s7 ∧
      (∀ (v : Fin 3) (k : ℕ), 2 ≤ k → N (some v) v k 0 m = (st m).s9) ∧
      (∀ (v : Fin 3) (k : ℕ), 2 ≤ k → N (some v) v k 1 m = (st m).s10) ∧
      (∀ (q p : Fin 3) (k : ℕ), 2 ≤ k → p ≠ q → N (some q) p k 1 m = (st m).s12) ∧
      (∀ (q p : Fin 3) (k : ℕ), 2 ≤ k → p ≠ q → N (some q) p k 0 m = (st m).s13) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, fun v k _ => ?_, fun v k _ => ?_, fun q p k _ hpq => ?_,
      fun q p k _ hpq => ?_⟩
    · simp [N_zero, lastBad, st]
    · simp [N_zero, lastBad, st]
    · simp [N_zero, lastBad, st]
    · simp [N_zero, lastBad, st]
    · simp [N_zero, lastBad, st, Ne.symm hpq]
    · simp [N_zero, lastBad, st, Ne.symm hpq]
  | succ m ih =>
    obtain ⟨h0, h7, h9, h10, h12, h13⟩ := ih
    refine ⟨?_, ?_, fun v k hk => ?_, fun v k hk => ?_, fun q p k hk hpq => ?_,
      fun q p k hk hpq => ?_⟩
    · rw [N_succ]
      simp [Fin.sum_univ_three, bad, h7, h12 0 1 2 (le_refl 2) (by decide), st]
    · rw [N_succ]
      simp [Fin.sum_univ_three, bad, h7, h13 0 1 2 (le_refl 2) (by decide), st]
    · rw [N_succ, s9_succ]
      have k1 : 1 ≤ k := by omega
      have m1 : max k 1 = k := by omega
      have m2 : max k 2 = k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases v <;>
        simp [Fin.sum_univ_three, bad, k1, hk, m1, m2, h9 _ k hk, h9 _ (max k 3) k3,
          h13 _ _ k hk, h13 _ _ (max k 3) k3] <;> ring
    · rw [N_succ, s10_succ]
      have k1 : 1 ≤ k := by omega
      have m1 : max k 1 = k := by omega
      have m2 : max k 2 = k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases v <;>
        simp [Fin.sum_univ_three, bad, k1, hk, m1, m2, h10 _ k hk, h10 _ (max k 3) k3,
          h12 _ _ k hk, h12 _ _ (max k 3) k3] <;> ring
    · rw [N_succ, s12_succ]
      have k1 : 1 ≤ k := by omega
      have m1 : max k 1 = k := by omega
      have m2 : max k 2 = k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases q <;> fin_cases p <;> simp at hpq ⊢ <;>
        simp [Fin.sum_univ_three, bad, k1, hk, m1, m2, h10 _ k hk, h10 _ (max k 3) k3]
    · rw [N_succ, s13_succ]
      have k1 : 1 ≤ k := by omega
      have m1 : max k 1 = k := by omega
      have m2 : max k 2 = k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases q <;> fin_cases p <;> simp at hpq ⊢ <;>
        simp [Fin.sum_univ_three, bad, k1, hk, m1, m2, h9 _ k hk, h9 _ (max k 3) k3,
          h12 _ _ k hk, h12 _ _ (max k 3) k3] <;> ring

theorem a_succ (n : ℕ) : a (n + 1) = (st n).s0 := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_three]
  simp only [valid]
  simp
  rw [← (N_eq n).1, N, Finset.card_filter]

/-- The defect of Barker's recurrence, in terms of the counts s0 = a(. + 1). -/
def B (j : ℕ) : ℤ :=
  (st (j + 4)).s0 - 2 * (st (j + 3)).s0 - 3 * (st (j + 2)).s0 + 4 * (st (j + 1)).s0 +
    4 * (st j).s0

theorem B_step (j : ℕ) : B (j + 2) = B (j + 1) := by
  simp only [B, st]
  push_cast
  ring

theorem B_zero (j : ℕ) : B (j + 1) = 0 := by
  induction j with
  | zero => decide
  | succ j ih => rw [B_step, ih]

theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 2 * a (n - 1) + 3 * a (n - 2) - 4 * a (n - 3) - 4 * a (n - 4) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  have h := B_zero j
  rw [show j + 6 - 1 = j + 4 + 1 by omega, show j + 6 - 2 = j + 3 + 1 by omega,
    show j + 6 - 3 = j + 2 + 1 by omega, show j + 6 - 4 = j + 1 + 1 by omega,
    show j + 6 = j + 5 + 1 by omega]
  simp only [a_succ]
  simp only [B] at h
  rw [show j + 1 + 4 = j + 5 by ring, show j + 1 + 3 = j + 4 by ring,
    show j + 1 + 2 = j + 3 by ring] at h
  linarith

theorem a_vals : a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 2 ∧ a 4 = 2 ∧ a 5 = 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: 2x^3(1 - x - x^2)/((1 + x)^2(1 - 2x)^2), in Q[[x]]. -/
theorem gf_eq : gf = 2 * X ^ 3 * (1 - X - X ^ 2) * ((1 + X) ^ 2 * (1 - 2 * X) ^ 2)⁻¹ := by
  set D : ℚ⟦X⟧ := (1 + X) ^ 2 * (1 - 2 * X) ^ 2 with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  obtain ⟨v1, v2, v3, v4, v5⟩ := a_vals
  have key : gf * D = 2 * X ^ 3 * (1 - X - X ^ 2) := by
    have e : gf * D = gf - C 2 * (gf * X ^ 1) - C 3 * (gf * X ^ 2) + C 4 * (gf * X ^ 3) +
        C 4 * (gf * X ^ 4) := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (2 : ℚ⟦X⟧) * X ^ 3 * (1 - X - X ^ 2) = C 2 * X ^ 3 - C 2 * X ^ 4 - C 2 * X ^ 5 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3, v4, v5] <;> norm_num
    · have hr := recurrence n hn
      have hq : (a n : ℚ) = 2 * a (n - 1) + 3 * a (n - 2) - 4 * a (n - 3) - 4 * a (n - 4) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show n ≠ 0 by omega,
        show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
        show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_false, coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- 108 a(n) = 8 (2^n - (-1)^n) + 3 n (2^n - 8 (-1)^n) for n >= 2. -/
def F (n : ℕ) : ℤ := 8 * ((-1) ^ (1 + n) + 2 ^ n) + 3 * (-8 * (-1) ^ n + 2 ^ n) * n

theorem F_rec (j : ℕ) :
    F (j + 6) = 2 * F (j + 5) + 3 * F (j + 4) - 4 * F (j + 3) - 4 * F (j + 2) := by
  simp only [F]
  push_cast
  ring

theorem closed_int (j : ℕ) :
    108 * (a (j + 2) : ℤ) = F (j + 2) ∧ 108 * (a (j + 3) : ℤ) = F (j + 3) ∧
      108 * (a (j + 4) : ℤ) = F (j + 4) ∧ 108 * (a (j + 5) : ℤ) = F (j + 5) := by
  induction j with
  | zero =>
    obtain ⟨-, v2, v3, v4, v5⟩ := a_vals
    simp only [zero_add, v2, v3, v4, v5, F]
    norm_num
  | succ j ih =>
    obtain ⟨h2, h3, h4, h5⟩ := ih
    refine ⟨h3, h4, h5, ?_⟩
    have hr := recurrence (j + 6) (by omega)
    rw [show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega] at hr
    show 108 * (a (j + 6) : ℤ) = F (j + 6)
    rw [hr, F_rec]
    linear_combination 2 * h5 + 3 * h4 - 4 * h3 - 4 * h2

/-- Barker's closed form, for n > 1. -/
theorem closed_form (n : ℕ) (hn : 1 < n) :
    (a n : ℚ) = (8 * ((-1) ^ (1 + n) + 2 ^ n) + 3 * (-8 * (-1) ^ n + 2 ^ n) * n) / 108 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have h := (closed_int j).1
  have hq : 108 * (a (j + 2) : ℚ) = (F (j + 2) : ℚ) := by exact_mod_cast h
  simp only [F] at hq
  push_cast at hq ⊢
  linear_combination hq / 108

/-- Both of Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    gf = 2 * X ^ 3 * (1 - X - X ^ 2) * ((1 + X) ^ 2 * (1 - 2 * X) ^ 2)⁻¹ ∧
    ∀ n : ℕ, 1 < n →
      (a n : ℚ) = (8 * ((-1) ^ (1 + n) + 2 ^ n) + 3 * (-8 * (-1) ^ n + 2 ^ n) * n) / 108 :=
  ⟨gf_eq, closed_form⟩

/-- Controls: a(1..17), the entry's data. -/
example : a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 2 ∧ a 4 = 2 ∧ a 5 = 8 ∧ a 6 = 14 ∧ a 7 = 36 ∧
    a 8 = 74 ∧ a 9 = 168 ∧ a 10 = 358 ∧ a 11 = 780 ∧ a 12 = 1666 ∧ a 13 = 3568 ∧
    a 14 = 7582 ∧ a 15 = 16084 ∧ a 16 = 33978 ∧ a 17 = 71608 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [a_succ] <;> rfl

/-- Control by direct enumeration of the 81 rows of length 4. -/
example : a 4 = 2 := by decide

end OMA.S_oeis_a280399

theorem OMA.solution : type_of% @OMA.S_oeis_a280399.main :=
  OMA.S_oeis_a280399.conjecture
