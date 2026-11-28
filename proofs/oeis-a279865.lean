import OMAStatements.S_oeis_a279865

namespace OMA.S_oeis_a279865

open PowerSeries







/-- Number of columns of length m that pass the scan from the state (q, p, k, e). -/
def N (q : Option (Fin 3)) (p : Fin 3) (k e m : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 3, if ok q p k e (List.ofFn y) = true then 1 else 0

theorem sum_cons (m : ℕ) (f : List (Fin 3) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 3, f (List.ofFn x) =
      ∑ c : Fin 3, ∑ y : Fin m → Fin 3, f (c :: List.ofFn y) := by
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
  simp [List.ofFn_succ]

theorem N_zero (q : Option (Fin 3)) (p : Fin 3) (k e : ℕ) :
    N q p k e 0 = if e + lastBad q p = 2 then 1 else 0 := by
  by_cases h : e + lastBad q p = 2 <;> simp [N, ok, h]

theorem N_succ (q : Option (Fin 3)) (p : Fin 3) (k e m : ℕ) :
    N q p k e (m + 1) = ∑ c : Fin 3, if c.val ≤ k ∧ e + bad q p c ≤ 2 then
      N (some p) c (max k (c.val + 1)) (e + bad q p c) m else 0 := by
  have h := sum_cons m (fun l => if ok q p k e l = true then 1 else 0)
  unfold N
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c.val ≤ k ∧ e + bad q p c ≤ 2
  · rw [if_pos hc]
    apply Finset.sum_congr rfl
    intro y _
    have e1 : ok q p k e (c :: List.ofFn y) =
        ok (some p) c (max k (c.val + 1)) (e + bad q p c) (List.ofFn y) := by
      show (decide (c.val ≤ k) && decide (e + bad q p c ≤ 2) && _) = _
      rw [decide_eq_true hc.1, decide_eq_true hc.2, Bool.true_and, Bool.true_and]
    rw [e1]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro y _
    have e1 : ok q p k e (c :: List.ofFn y) = false := by
      show (decide (c.val ≤ k) && decide (e + bad q p c ≤ 2) && _) = false
      by_cases h1 : c.val ≤ k
      · have h2 : ¬ (e + bad q p c ≤ 2) := fun h2 => hc ⟨h1, h2⟩
        rw [decide_eq_false h2, Bool.and_false, Bool.false_and]
      · rw [decide_eq_false h1, Bool.false_and, Bool.false_and]
    simp [e1]

/-- Counts by class: g0 from (none, 0, 1, 0), g1 from (some 0, 0, 1, 0), g3, g19, g18 from
(some q, p, k, e) with p ≠ q, k >= 2 and e = 0, 1, 2, and g14, g15, g16 from (some v, v, k, e)
with k >= 2 and e = 0, 1, 2. -/
structure S where
  g0 : ℕ
  g1 : ℕ
  g3 : ℕ
  g14 : ℕ
  g15 : ℕ
  g16 : ℕ
  g18 : ℕ
  g19 : ℕ

def st : ℕ → S
  | 0 => ⟨0, 0, 0, 0, 0, 1, 0, 1⟩
  | m + 1 =>
    let s := st m
    ⟨s.g1 + s.g19, s.g1 + s.g3, s.g14 + 2 * s.g19, s.g14 + 2 * s.g3, s.g15 + 2 * s.g19,
      s.g16 + 2 * s.g18, s.g16, 2 * s.g18 + s.g15⟩

theorem g3_succ (m : ℕ) : (st (m + 1)).g3 = (st m).g14 + 2 * (st m).g19 := rfl
theorem g14_succ (m : ℕ) : (st (m + 1)).g14 = (st m).g14 + 2 * (st m).g3 := rfl
theorem g15_succ (m : ℕ) : (st (m + 1)).g15 = (st m).g15 + 2 * (st m).g19 := rfl
theorem g16_succ (m : ℕ) : (st (m + 1)).g16 = (st m).g16 + 2 * (st m).g18 := rfl
theorem g18_succ (m : ℕ) : (st (m + 1)).g18 = (st m).g16 := rfl
theorem g19_succ (m : ℕ) : (st (m + 1)).g19 = 2 * (st m).g18 + (st m).g15 := rfl

theorem N_eq (m : ℕ) :
    N none 0 1 0 m = (st m).g0 ∧ N (some 0) 0 1 0 m = (st m).g1 ∧
      (∀ (q p : Fin 3) (k : ℕ), 2 ≤ k → p ≠ q → N (some q) p k 0 m = (st m).g3) ∧
      (∀ (v : Fin 3) (k : ℕ), 2 ≤ k → N (some v) v k 0 m = (st m).g14) ∧
      (∀ (v : Fin 3) (k : ℕ), 2 ≤ k → N (some v) v k 1 m = (st m).g15) ∧
      (∀ (v : Fin 3) (k : ℕ), 2 ≤ k → N (some v) v k 2 m = (st m).g16) ∧
      (∀ (q p : Fin 3) (k : ℕ), 2 ≤ k → p ≠ q → N (some q) p k 2 m = (st m).g18) ∧
      (∀ (q p : Fin 3) (k : ℕ), 2 ≤ k → p ≠ q → N (some q) p k 1 m = (st m).g19) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, fun q p k _ hpq => ?_, fun v k _ => ?_, fun v k _ => ?_, fun v k _ => ?_,
      fun q p k _ hpq => ?_, fun q p k _ hpq => ?_⟩
    · simp [N_zero, lastBad, st]
    · simp [N_zero, lastBad, st]
    · simp [N_zero, lastBad, st, Ne.symm hpq]
    · simp [N_zero, lastBad, st]
    · simp [N_zero, lastBad, st]
    · simp [N_zero, lastBad, st]
    · simp [N_zero, lastBad, st, Ne.symm hpq]
    · simp [N_zero, lastBad, st, Ne.symm hpq]
  | succ m ih =>
    obtain ⟨h0, h1, h3, h14, h15, h16, h18, h19⟩ := ih
    refine ⟨?_, ?_, fun q p k hk hpq => ?_, fun v k hk => ?_, fun v k hk => ?_, fun v k hk => ?_,
      fun q p k hk hpq => ?_, fun q p k hk hpq => ?_⟩
    · rw [N_succ]
      simp [Fin.sum_univ_three, bad, h1, h19 0 1 2 (le_refl 2) (by decide), st]
    · rw [N_succ]
      simp [Fin.sum_univ_three, bad, h1, h3 0 1 2 (le_refl 2) (by decide), st]
    · rw [N_succ, g3_succ]
      have k1 : 1 ≤ k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases q <;> fin_cases p <;> simp at hpq ⊢ <;>
        simp [Fin.sum_univ_three, bad, k1, hk, h14 _ k hk, h14 _ (max k 3) k3,
          h19 _ _ k hk, h19 _ _ (max k 3) k3] <;> ring
    · rw [N_succ, g14_succ]
      have k1 : 1 ≤ k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases v <;>
        simp [Fin.sum_univ_three, bad, k1, hk, h14 _ k hk, h14 _ (max k 3) k3,
          h3 _ _ k hk, h3 _ _ (max k 3) k3] <;> ring
    · rw [N_succ, g15_succ]
      have k1 : 1 ≤ k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases v <;>
        simp [Fin.sum_univ_three, bad, k1, hk, h15 _ k hk, h15 _ (max k 3) k3,
          h19 _ _ k hk, h19 _ _ (max k 3) k3] <;> ring
    · rw [N_succ, g16_succ]
      have k1 : 1 ≤ k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases v <;>
        simp [Fin.sum_univ_three, bad, k1, hk, h16 _ k hk, h16 _ (max k 3) k3,
          h18 _ _ k hk, h18 _ _ (max k 3) k3] <;> ring
    · rw [N_succ, g18_succ]
      have k1 : 1 ≤ k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases q <;> fin_cases p <;> simp at hpq ⊢ <;>
        simp [Fin.sum_univ_three, bad, k1, hk, h16 _ k hk, h16 _ (max k 3) k3]
    · rw [N_succ, g19_succ]
      have k1 : 1 ≤ k := by omega
      have k3 : 2 ≤ max k 3 := le_max_of_le_left hk
      fin_cases q <;> fin_cases p <;> simp at hpq ⊢ <;>
        simp [Fin.sum_univ_three, bad, k1, hk, h15 _ k hk, h15 _ (max k 3) k3,
          h18 _ _ k hk, h18 _ _ (max k 3) k3] <;> ring

theorem a_succ (n : ℕ) : a (n + 1) = (st n).g0 := by
  have h := sum_cons n (fun l => if valid l = true then 1 else 0)
  unfold a
  rw [Finset.card_filter, h, Fin.sum_univ_three]
  simp only [valid]
  simp
  rw [← (N_eq n).1, N, Finset.card_filter]

/-- The defect of Barker's recurrence, in terms of the counts g0 = a(. + 1). -/
def B (j : ℕ) : ℤ :=
  (st (j + 6)).g0 - 3 * (st (j + 5)).g0 - 3 * (st (j + 4)).g0 + 11 * (st (j + 3)).g0 +
    6 * (st (j + 2)).g0 - 12 * (st (j + 1)).g0 - 8 * (st j).g0

theorem B_step (j : ℕ) : B (j + 2) = B (j + 1) := by
  simp only [B, st]
  push_cast
  ring

theorem B_zero (j : ℕ) : B (j + 1) = 0 := by
  induction j with
  | zero => decide
  | succ j ih => rw [B_step, ih]

theorem a_vals : a 1 = 0 ∧ a 2 = 1 ∧ a 3 = 0 ∧ a 4 = 6 ∧ a 5 = 6 ∧ a 6 = 30 ∧ a 7 = 54 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_succ] <;> rfl

theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℤ) = 3 * a (n - 1) + 3 * a (n - 2) - 11 * a (n - 3) - 6 * a (n - 4) +
      12 * a (n - 5) + 8 * a (n - 6) := by
  rcases Nat.lt_or_ge n 8 with h8 | h8
  · obtain rfl : n = 7 := by omega
    obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := a_vals
    simp [v1, v2, v3, v4, v5, v6, v7]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
    have h : ((st (j + 7)).g0 : ℤ) - 3 * (st (j + 6)).g0 - 3 * (st (j + 5)).g0 +
        11 * (st (j + 4)).g0 + 6 * (st (j + 3)).g0 - 12 * (st (j + 2)).g0 -
        8 * (st (j + 1)).g0 = 0 := B_zero j
    rw [show j + 8 - 1 = j + 6 + 1 by omega, show j + 8 - 2 = j + 5 + 1 by omega,
      show j + 8 - 3 = j + 4 + 1 by omega, show j + 8 - 4 = j + 3 + 1 by omega,
      show j + 8 - 5 = j + 2 + 1 by omega, show j + 8 - 6 = j + 1 + 1 by omega,
      show j + 8 = j + 7 + 1 by omega]
    simp only [a_succ]
    linarith

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (a n : ℚ) := by simp [gf]

/-- Barker's g.f.: x^2(1 - x)^3/((1 + x)^3(1 - 2x)^3), in Q[[x]]. -/
theorem gf_eq : gf = X ^ 2 * (1 - X) ^ 3 * ((1 + X) ^ 3 * (1 - 2 * X) ^ 3)⁻¹ := by
  set D : ℚ⟦X⟧ := (1 + X) ^ 3 * (1 - 2 * X) ^ 3 with hD
  have hden : constantCoeff D ≠ 0 := by rw [hD]; simp
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := a_vals
  have key : gf * D = X ^ 2 * (1 - X) ^ 3 := by
    have e : gf * D = gf - C 3 * (gf * X ^ 1) - C 3 * (gf * X ^ 2) + C 11 * (gf * X ^ 3) +
        C 6 * (gf * X ^ 4) - C 12 * (gf * X ^ 5) - C 8 * (gf * X ^ 6) := by
      rw [hD]; simp only [map_ofNat]; ring
    have en : (X : ℚ⟦X⟧) ^ 2 * (1 - X) ^ 3 = X ^ 2 - C 3 * X ^ 3 + C 3 * X ^ 4 - X ^ 5 := by
      simp only [map_ofNat]; ring
    rw [e, en]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_gf, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6] <;> norm_num
    · have hr := recurrence n hn
      have hq : (a n : ℚ) = 3 * a (n - 1) + 3 * a (n - 2) - 11 * a (n - 3) - 6 * a (n - 4) +
          12 * a (n - 5) + 8 * a (n - 6) := by
        exact_mod_cast hr
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, if_true,
        show n ≠ 0 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
        show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
        show n - 6 ≠ 0 by omega, if_false, show n ≠ 2 by omega, show n ≠ 5 by omega, coeff_C]
      linarith
  calc gf = gf * (D * D⁻¹) := by rw [PowerSeries.mul_inv_cancel _ hden, mul_one]
    _ = (gf * D) * D⁻¹ := (mul_assoc gf _ _).symm
    _ = _ := by rw [key]

/-- 648 a(n) = 2^n (3n^2 + 21n + 16) + (-1)^n (96n^2 - 16) for n >= 1. -/
def F (n : ℕ) : ℤ := 2 ^ n * (3 * n ^ 2 + 21 * n + 16) + (-1) ^ n * (96 * n ^ 2 - 16)

theorem F_rec (j : ℕ) :
    F (j + 7) = 3 * F (j + 6) + 3 * F (j + 5) - 11 * F (j + 4) - 6 * F (j + 3) +
      12 * F (j + 2) + 8 * F (j + 1) := by
  simp only [F]
  push_cast
  ring

theorem closed_int (j : ℕ) :
    648 * (a (j + 1) : ℤ) = F (j + 1) ∧ 648 * (a (j + 2) : ℤ) = F (j + 2) ∧
      648 * (a (j + 3) : ℤ) = F (j + 3) ∧ 648 * (a (j + 4) : ℤ) = F (j + 4) ∧
      648 * (a (j + 5) : ℤ) = F (j + 5) ∧ 648 * (a (j + 6) : ℤ) = F (j + 6) := by
  induction j with
  | zero =>
    obtain ⟨v1, v2, v3, v4, v5, v6, -⟩ := a_vals
    simp only [zero_add, v1, v2, v3, v4, v5, v6, F]
    norm_num
  | succ j ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    refine ⟨h2, h3, h4, h5, h6, ?_⟩
    have hr := recurrence (j + 7) (by omega)
    rw [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega, show j + 7 - 4 = j + 3 by omega,
      show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega] at hr
    show 648 * (a (j + 7) : ℤ) = F (j + 7)
    rw [hr, F_rec]
    linear_combination 3 * h6 + 3 * h5 - 11 * h4 - 6 * h3 + 12 * h2 + 8 * h1

theorem closed_even (n : ℕ) (h1 : 1 ≤ n) (he : Even n) :
    (a n : ℚ) = (3 * 2 ^ n * n ^ 2 + 96 * n ^ 2 + 21 * 2 ^ n * n + 2 ^ (n + 4) - 16) / 648 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (closed_int m).1
  have hq : 648 * (a (m + 1) : ℚ) = (F (m + 1) : ℚ) := by exact_mod_cast h
  simp only [F] at hq
  push_cast at hq
  rw [Even.neg_one_pow he] at hq
  push_cast
  linear_combination hq / 648

theorem closed_odd (n : ℕ) (h1 : 1 ≤ n) (ho : Odd n) :
    (a n : ℚ) = (3 * 2 ^ n * n ^ 2 - 96 * n ^ 2 + 21 * 2 ^ n * n + 2 ^ (n + 4) + 16) / 648 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (closed_int m).1
  have hq : 648 * (a (m + 1) : ℚ) = (F (m + 1) : ℚ) := by exact_mod_cast h
  simp only [F] at hq
  push_cast at hq
  rw [Odd.neg_one_pow ho] at hq
  push_cast
  linear_combination hq / 648

/-- Barker's three conjectures. -/
theorem conjecture :
    gf = X ^ 2 * (1 - X) ^ 3 * ((1 + X) ^ 3 * (1 - 2 * X) ^ 3)⁻¹ ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) =
      (3 * 2 ^ n * n ^ 2 + 96 * n ^ 2 + 21 * 2 ^ n * n + 2 ^ (n + 4) - 16) / 648) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) =
      (3 * 2 ^ n * n ^ 2 - 96 * n ^ 2 + 21 * 2 ^ n * n + 2 ^ (n + 4) + 16) / 648) :=
  ⟨gf_eq, closed_even, closed_odd⟩

/-- Controls: a(1..16), the entry's data. -/
example : a 1 = 0 ∧ a 2 = 1 ∧ a 3 = 0 ∧ a 4 = 6 ∧ a 5 = 6 ∧ a 6 = 30 ∧ a 7 = 54 ∧
    a 8 = 158 ∧ a 9 = 342 ∧ a 10 = 846 ∧ a 11 = 1910 ∧ a 12 = 4446 ∧ a 13 = 10038 ∧
    a 14 = 22734 ∧ a 15 = 50838 ∧ a 16 = 113310 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [a_succ] <;> rfl

/-- Control by direct enumeration of the 81 columns of length 4. -/
example : a 4 = 6 := by decide

end OMA.S_oeis_a279865

theorem OMA.solution : type_of% @OMA.S_oeis_a279865.main :=
  OMA.S_oeis_a279865.conjecture
