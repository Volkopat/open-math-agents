import OMAStatements.S_oeis_a250461
import Mathlib

open OMA.S_oeis_a250461 PowerSeries

namespace P250461

def okR (r s : Fin 2 → Fin 2) : Prop := okBlock (r 0) (r 1) (s 0) (s 1)

instance (r s : Fin 2 → Fin 2) : Decidable (okR r s) := by unfold okR; infer_instance

def V (m : ℕ) (f : Fin (m + 1) → Fin 2 → Fin 2) : Prop := ∀ i : Fin m, okR (f i.castSucc) (f i.succ)

instance (m : ℕ) (f : Fin (m + 1) → Fin 2 → Fin 2) : Decidable (V m f) := by unfold V; infer_instance

theorem valid_iff (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 2) : isValid m x ↔ V m x := by
  constructor
  · intro h i
    exact h i 0
  · intro h i j
    fin_cases j
    exact h i

theorem V_cons (m : ℕ) (r : Fin 2 → Fin 2) (y : Fin (m + 1) → Fin 2 → Fin 2) :
    V (m + 1) (Fin.cons r y : Fin (m + 2) → Fin 2 → Fin 2) ↔ okR r (y 0) ∧ V m y := by
  unfold V
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Fin 2 → Fin 2) → ℕ) :
    ∑ f, F f = ∑ x : Fin 2 → Fin 2, ∑ g : Fin n → Fin 2 → Fin 2, F (Fin.cons x g) := by
  rw [← (Fin.consEquiv (fun _ => Fin 2 → Fin 2)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sumR (g : (Fin 2 → Fin 2) → ℕ) :
    ∑ s, g s = g ![0, 0] + g ![0, 1] + g ![1, 0] + g ![1, 1] := by
  have e : ∀ a b : Fin 2, (piFinTwoEquiv fun _ => Fin 2).symm (a, b) = ![a, b] := by
    intro a b
    funext i
    fin_cases i <;> rfl
  rw [← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, e]
  ring

def H (m : ℕ) (r : Fin 2 → Fin 2) : ℕ :=
  ∑ y : Fin m → Fin 2 → Fin 2, if V m (Fin.cons r y : Fin (m + 1) → Fin 2 → Fin 2) then 1 else 0

theorem H_succ (m : ℕ) (r : Fin 2 → Fin 2) :
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

theorem H0 (r : Fin 2 → Fin 2) : H 0 r = 1 := by
  rw [H, Fintype.sum_unique, if_pos]
  intro i
  exact i.elim0

theorem Hs (m : ℕ) :
    H (m + 1) ![0, 0] = H m ![0, 0] + H m ![0, 1] + H m ![1, 0] + H m ![1, 1] ∧
    H (m + 1) ![0, 1] = H m ![0, 0] + H m ![0, 1] + H m ![1, 0] + H m ![1, 1] ∧
    H (m + 1) ![1, 0] = H m ![0, 0] + H m ![0, 1] ∧
    H (m + 1) ![1, 1] = H m ![1, 1] := by
  simp only [H_succ, sumR]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [okR, okBlock]

theorem H11 (m : ℕ) : H m ![1, 1] = 1 := by
  induction m with
  | zero => exact H0 _
  | succ m ih => rw [(Hs m).2.2.2, ih]

def S (m : ℕ) : ℕ := H m ![0, 0] + H m ![0, 1] + H m ![1, 0] + H m ![1, 1]

theorem S0 : S 0 = 4 := by simp [S, H0]

theorem S1 : S 1 = 11 := by
  obtain ⟨e1, e2, e3, e4⟩ := Hs 0
  simp only [S, e1, e2, e3, e4, H0]

theorem Srec (m : ℕ) : S (m + 2) = 2 * S (m + 1) + 2 * S m + 1 := by
  obtain ⟨e1, e2, e3, e4⟩ := Hs (m + 1)
  obtain ⟨f1, f2, f3, f4⟩ := Hs m
  have h1 := H11 m
  have h2 := H11 (m + 1)
  show S (m + 1 + 1) = 2 * S (m + 1) + 2 * S m + 1
  simp only [S]
  omega

theorem aS (n : ℕ) : a (n + 1) = S (n + 1) := by
  rw [a, Finset.card_filter]
  simp only [valid_iff]
  rw [sum_cons, sumR]
  rfl

theorem S2 : S 2 = 31 := by rw [Srec 0, S1, S0]
theorem S3 : S 3 = 85 := by rw [Srec 1, S2, S1]

theorem rec3 (k : ℕ) : (a (k + 4) : ℤ) = 3 * a (k + 3) - 2 * a (k + 1) := by
  have a4 : a (k + 4) = S (k + 4) := aS (k + 3)
  have a3 : a (k + 3) = S (k + 3) := aS (k + 2)
  have a1 : a (k + 1) = S (k + 1) := aS k
  have h1 : S (k + 4) = 2 * S (k + 3) + 2 * S (k + 2) + 1 := Srec (k + 2)
  have h2 : S (k + 3) = 2 * S (k + 2) + 2 * S (k + 1) + 1 := Srec (k + 1)
  rw [a4, a3, a1]
  push_cast
  omega

theorem av0 : a 0 = 0 := rfl
theorem av1 : a 1 = 11 := by rw [aS, S1]
theorem av2 : a 2 = 31 := by rw [aS, S2]
theorem av3 : a 3 = 85 := by rw [aS, S3]

noncomputable def F (n : ℕ) : ℝ :=
  (-2 + (13 - 7 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n + (1 + Real.sqrt 3) ^ n * (13 + 7 * Real.sqrt 3)) / 6

theorem frec (k : ℕ) : F (k + 3) = 3 * F (k + 2) - 2 * F k := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold F
  linear_combination (((13 - 7 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ k * (-Real.sqrt 3) +
    (1 + Real.sqrt 3) ^ k * (13 + 7 * Real.sqrt 3) * Real.sqrt 3) / 6) * hs

theorem freal (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = F n := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with h | h | h | h
    · subst h; rw [av1]; unfold F; push_cast; linear_combination (-(7 / 3 : ℝ)) * hs
    · subst h; rw [av2]; unfold F; push_cast; linear_combination (-9 : ℝ) * hs
    · subst h; rw [av3]; unfold F; push_cast
      linear_combination (-(27 + 7 / 3 * Real.sqrt 3 ^ 2) : ℝ) * hs
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have h := rec3 k
      have h' : ((a (k + 4) : ℤ) : ℝ) = ((3 * a (k + 3) - 2 * a (k + 1) : ℤ) : ℝ) := by rw [h]
      push_cast at h'
      have hf : F (k + 4) = 3 * F (k + 3) - 2 * F (k + 1) := frec (k + 1)
      rw [h', ih (k + 3) (by omega) (by omega), ih (k + 1) (by omega) (by omega), hf]

end P250461

theorem OMA.solution : type_of% @OMA.S_oeis_a250461.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 3 = k + 1 by omega]
    exact P250461.rec3 k
  · have hL : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X - 2 * X ^ 2)) : PowerSeries ℚ) = PowerSeries.mk (fun n => (a n : ℚ)) - C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    have hR : (X * (11 - 2 * X - 8 * X ^ 2) : PowerSeries ℚ) = C (11 : ℚ) * X ^ 1 - C (2 : ℚ) * X ^ 2 - C (8 : ℚ) * X ^ 3 := by
      (try simp only [map_ofNat, map_one, map_neg, one_mul, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | n
    · norm_num [P250461.av0, P250461.av1, P250461.av2, P250461.av3]
    · norm_num [P250461.av0, P250461.av1, P250461.av2, P250461.av3]
    · norm_num [P250461.av0, P250461.av1, P250461.av2, P250461.av3]
    · norm_num [P250461.av0, P250461.av1, P250461.av2, P250461.av3]
    · simp only [show n + 1 + 1 + 1 + 1 = n + 4 by omega]
      simp only [show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega, show n + 4 - 3 = n + 1 by omega]
      try simp only [show (n + 4 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 1) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 2) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 3) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      try simp only [show (n + 1 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 2 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 3 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, show (n + 4 = 0) = False by simp only [eq_iff_iff, iff_false]; omega, if_false]
      try simp only [show 1 ≤ n + 4 by omega, show 2 ≤ n + 4 by omega, show 3 ≤ n + 4 by omega, if_true]
      have h := P250461.rec3 n
      have h' : ((a (n + 4) : ℤ) : ℚ) = ((3 * a (n + 3) - 2 * a (n + 1) : ℤ) : ℚ) := by rw [h]
      push_cast at h'
      push_cast
      linarith
  · intro n hn
    exact P250461.freal n hn
