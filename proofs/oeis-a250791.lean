import OMAStatements.S_oeis_a250791
import Mathlib

open OMA.S_oeis_a250791 PowerSeries

namespace P250791

def okR (r s : Fin 3 → Fin 2) : Prop :=
  okBlock (r 0) (r 1) (s 0) (s 1) ∧ okBlock (r 1) (r 2) (s 1) (s 2)

instance (r s : Fin 3 → Fin 2) : Decidable (okR r s) := by unfold okR; infer_instance

def V (m : ℕ) (f : Fin (m + 1) → Fin 3 → Fin 2) : Prop := ∀ i : Fin m, okR (f i.castSucc) (f i.succ)

instance (m : ℕ) (f : Fin (m + 1) → Fin 3 → Fin 2) : Decidable (V m f) := by unfold V; infer_instance

theorem valid_iff (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 2) : isValid m x ↔ V m x := by
  constructor
  · intro h i
    exact ⟨h i 0, h i 1⟩
  · intro h i j
    fin_cases j
    · exact (h i).1
    · exact (h i).2

theorem V_cons (m : ℕ) (r : Fin 3 → Fin 2) (y : Fin (m + 1) → Fin 3 → Fin 2) :
    V (m + 1) (Fin.cons r y : Fin (m + 2) → Fin 3 → Fin 2) ↔ okR r (y 0) ∧ V m y := by
  unfold V
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 3 → Fin 2) → ℕ) :
    ∑ f, F f = ∑ x : Fin 3 → Fin 2, ∑ g : Fin n → Fin 3 → Fin 2, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 3 → Fin 2)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sumR2 (g : (Fin 2 → Fin 2) → ℕ) :
    ∑ s, g s = g ![0, 0] + g ![0, 1] + g ![1, 0] + g ![1, 1] := by
  have e : ∀ a b : Fin 2, (piFinTwoEquiv fun _ => Fin 2).symm (a, b) = ![a, b] := by
    intro a b
    funext i
    fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, e]
  ring

theorem sumR (g : (Fin 3 → Fin 2) → ℕ) :
    ∑ s, g s = g ![0, 0, 0] + g ![0, 0, 1] + g ![0, 1, 0] + g ![0, 1, 1] + g ![1, 0, 0] + g ![1, 0, 1] + g ![1, 1, 0] + g ![1, 1, 1] := by
  rw [← (Fin.consEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [sumR2, sumR2]
  try simp only [Fin.consEquiv_apply]
  ring_nf
  rfl

def H (m : ℕ) (r : Fin 3 → Fin 2) : ℕ :=
  ∑ y : Fin m → Fin 3 → Fin 2, if V m (Fin.cons r y : Fin (m + 1) → Fin 3 → Fin 2) then 1 else 0

theorem H_succ (m : ℕ) (r : Fin 3 → Fin 2) :
    H (m + 1) r = ∑ s, if okR r s then H m s else 0 := by
  rw [H, sum_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : okR r s
  · rw [if_pos hs, H]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [V_cons, Fin.cons_zero, hs, true_and]
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [V_cons, Fin.cons_zero, hs]

theorem H0 (r : Fin 3 → Fin 2) : H 0 r = 1 := by
  rw [H, Fintype.sum_unique, if_pos]
  intro i
  exact i.elim0

theorem Hs (m : ℕ) :
    H (m + 1) ![0, 0, 0] = H m ![0, 0, 0] + H m ![0, 0, 1] + H m ![0, 1, 1] + H m ![1, 1, 1] ∧
    H (m + 1) ![0, 0, 1] = H m ![0, 0, 0] + H m ![0, 0, 1] + H m ![0, 1, 0] + H m ![1, 1, 0] ∧
    H (m + 1) ![0, 1, 0] = H m ![0, 0, 1] + H m ![0, 1, 0] + H m ![0, 1, 1] + H m ![1, 0, 1] ∧
    H (m + 1) ![0, 1, 1] = H m ![0, 1, 1] ∧
    H (m + 1) ![1, 0, 0] = H m ![0, 1, 1] + H m ![1, 0, 0] + H m ![1, 0, 1] + H m ![1, 1, 1] ∧
    H (m + 1) ![1, 0, 1] = H m ![0, 1, 0] + H m ![1, 0, 0] + H m ![1, 0, 1] + H m ![1, 1, 0] ∧
    H (m + 1) ![1, 1, 0] = H m ![1, 1, 0] + H m ![1, 1, 1] ∧
    H (m + 1) ![1, 1, 1] = H m ![1, 1, 1] := by
  simp only [H_succ, sumR]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [okR, okBlock, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

def S (m : ℕ) : ℕ := H m ![0, 0, 0] + H m ![0, 0, 1] + H m ![0, 1, 0] + H m ![0, 1, 1] + H m ![1, 0, 0] + H m ![1, 0, 1] + H m ![1, 1, 0] + H m ![1, 1, 1]

theorem aS (n : ℕ) : a (n + 1) = S (n + 1) := by
  rw [a, Finset.card_filter]
  simp only [valid_iff]
  rw [sum_cons, sumR]
  rfl

theorem Srec (m : ℕ) : (S (m + 4) : ℤ) = 4 * S (m + 3) - 3 * S (m + 2) - 2 * S (m + 1) + 2 * S m := by
  have h0 := Hs m
  have h1 := Hs (m + 1)
  have h2 := Hs (m + 2)
  have h3 := Hs (m + 3)
  simp only [show m + 1 + 1 = m + 2 from rfl, show m + 2 + 1 = m + 3 from rfl,
    show m + 3 + 1 = m + 4 from rfl] at h1 h2 h3
  simp only [S]
  omega

theorem S0 : S 0 = 8 := by simp [S, H0]
theorem S1 : S 1 = 24 := by
  have h0 := Hs 0
  simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
    show (2 : ℕ) + 1 = 3 from rfl, H0] at *
  simp only [S]
  omega
theorem S2 : S 2 = 66 := by
  have h0 := Hs 0
  have h1 := Hs 1
  simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
    show (2 : ℕ) + 1 = 3 from rfl, H0] at *
  simp only [S]
  omega
theorem S3 : S 3 = 180 := by
  have h0 := Hs 0
  have h1 := Hs 1
  have h2 := Hs 2
  simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
    show (2 : ℕ) + 1 = 3 from rfl, H0] at *
  simp only [S]
  omega
theorem S4 : S 4 = 490 := by
  have h : (S 4 : ℤ) = 4 * S 3 - 3 * S 2 - 2 * S 1 + 2 * S 0 := Srec 0
  rw [S3, S2, S1, S0] at h
  omega

theorem rec4 (k : ℕ) : (a (k + 5) : ℤ) = 4 * a (k + 4) - 3 * a (k + 3) - 2 * a (k + 2) + 2 * a (k + 1) := by
  have a5 : a (k + 5) = S (k + 5) := aS (k + 4)
  have a4 : a (k + 4) = S (k + 4) := aS (k + 3)
  have a3 : a (k + 3) = S (k + 3) := aS (k + 2)
  have a2 : a (k + 2) = S (k + 2) := aS (k + 1)
  have a1 : a (k + 1) = S (k + 1) := aS k
  have h : (S (k + 5) : ℤ) = 4 * S (k + 4) - 3 * S (k + 3) - 2 * S (k + 2) + 2 * S (k + 1) := Srec (k + 1)
  rw [a5, a4, a3, a2, a1]
  exact h

theorem av0 : a 0 = 0 := rfl
theorem av1 : a 1 = 24 := by rw [aS, S1]
theorem av2 : a 2 = 66 := by rw [aS, S2]
theorem av3 : a 3 = 180 := by rw [aS, S3]
theorem av4 : a 4 = 490 := by rw [aS, S4]

noncomputable def F (n : ℕ) : ℝ :=
  (-6 + (39 - 23 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n + 39 * (1 + Real.sqrt 3) ^ n +
    23 * Real.sqrt 3 * (1 + Real.sqrt 3) ^ n + 6 * (n : ℝ)) / 9

theorem frec (k : ℕ) : F (k + 4) = 4 * F (k + 3) - 3 * F (k + 2) - 2 * F (k + 1) + 2 * F k := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold F
  push_cast
  linear_combination (((39 - 23 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ k * Real.sqrt 3 ^ 2 +
    (39 + 23 * Real.sqrt 3) * (1 + Real.sqrt 3) ^ k * Real.sqrt 3 ^ 2) / 9) * hs

theorem freal (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = F n := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with h | h | h | h | h
    · subst h; rw [av1]; unfold F; push_cast; linear_combination (-(46 / 9 : ℝ)) * hs
    · subst h; rw [av2]; unfold F; push_cast; linear_combination (-(170 / 9 : ℝ)) * hs
    · subst h; rw [av3]; unfold F; push_cast
      linear_combination (-(170 / 3 + 46 / 9 * Real.sqrt 3 ^ 2) : ℝ) * hs
    · subst h; rw [av4]; unfold F; push_cast
      linear_combination (-(1438 / 9 + 262 / 9 * Real.sqrt 3 ^ 2) : ℝ) * hs
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have h := rec4 k
      have h' : ((a (k + 5) : ℤ) : ℝ) = ((4 * a (k + 4) - 3 * a (k + 3) - 2 * a (k + 2) + 2 * a (k + 1) : ℤ) : ℝ) := by rw [h]
      push_cast at h'
      have hf : F (k + 5) = 4 * F (k + 4) - 3 * F (k + 3) - 2 * F (k + 2) + 2 * F (k + 1) := frec (k + 1)
      rw [h', ih (k + 4) (by omega) (by omega), ih (k + 3) (by omega) (by omega),
        ih (k + 2) (by omega) (by omega), ih (k + 1) (by omega) (by omega), hf]

end P250791

theorem OMA.solution : type_of% @OMA.S_oeis_a250791.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega,
      show k + 5 - 4 = k + 1 by omega]
    exact P250791.rec4 k
  · have hL : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 - 2 * X - 2 * X ^ 2)) : PowerSeries ℚ) = PowerSeries.mk (fun n => (a n : ℚ)) - C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) + C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    have hR : (2 * X * (12 - 15 * X - 6 * X ^ 2 + 8 * X ^ 3) : PowerSeries ℚ) = C (24 : ℚ) * X ^ 1 - C (30 : ℚ) * X ^ 2 - C (12 : ℚ) * X ^ 3 + C (16 : ℚ) * X ^ 4 := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | n
    · norm_num [P250791.av0, P250791.av1, P250791.av2, P250791.av3, P250791.av4]
    · norm_num [P250791.av0, P250791.av1, P250791.av2, P250791.av3, P250791.av4]
    · norm_num [P250791.av0, P250791.av1, P250791.av2, P250791.av3, P250791.av4]
    · norm_num [P250791.av0, P250791.av1, P250791.av2, P250791.av3, P250791.av4]
    · norm_num [P250791.av0, P250791.av1, P250791.av2, P250791.av3, P250791.av4]
    · simp only [show n + 1 + 1 + 1 + 1 + 1 = n + 5 by omega]
      simp only [show n + 5 - 1 = n + 4 by omega, show n + 5 - 2 = n + 3 by omega, show n + 5 - 3 = n + 2 by omega, show n + 5 - 4 = n + 1 by omega]
      try simp only [show (n + 5 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 5 = 1) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 5 = 2) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 5 = 3) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 5 = 4) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      try simp only [show (n + 1 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 2 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 3 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 5 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      try simp only [show 1 ≤ n + 5 by omega, show 2 ≤ n + 5 by omega, show 3 ≤ n + 5 by omega, show 4 ≤ n + 5 by omega, if_true]
      have h := P250791.rec4 n
      have h' : ((a (n + 5) : ℤ) : ℚ) = ((4 * a (n + 4) - 3 * a (n + 3) - 2 * a (n + 2) + 2 * a (n + 1) : ℤ) : ℚ) := by rw [h]
      push_cast at h'
      push_cast
      linarith
  · intro n hn
    exact P250791.freal n hn
