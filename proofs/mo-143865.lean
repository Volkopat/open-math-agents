import OMAStatements.S_mo_143865
import Mathlib

-- Problem: Asymptotic growth of recurrence relation (mo-143865)
-- Credit: @kintonc

namespace ProofMO143865

open OMA.S_mo_143865

lemma recurs_unique {a : ℝ} {x y : ℕ → ℝ} (hx : Recurs a x) (hy : Recurs a y) :
    ∀ n : ℕ, 1 ≤ n → x n = y n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases eq_or_lt_of_le hn with rfl | hn2
    · rw [hx.1, hy.1]
    · have hn2' : 2 ≤ n := hn2
      have hcost : ∀ i j : ℕ, 0 < i → 0 < j → i + j = n → cost a x i j = cost a y i j := by
        intro i j hi hj hij
        simp only [cost]
        rw [ih i (by omega) hi, ih j (by omega) hj]
      obtain ⟨i₁, j₁, hi₁, hj₁, hij₁, hx₁⟩ := (hx.2 n hn2').2
      obtain ⟨i₂, j₂, hi₂, hj₂, hij₂, hy₂⟩ := (hy.2 n hn2').2
      have h1 : y n ≤ x n := by
        rw [hx₁, hcost i₁ j₁ hi₁ hj₁ hij₁]
        exact (hy.2 n hn2').1 i₁ j₁ hi₁ hj₁ hij₁
      have h2 : x n ≤ y n := by
        rw [hy₂, ← hcost i₂ j₂ hi₂ hj₂ hij₂]
        exact (hx.2 n hn2').1 i₂ j₂ hi₂ hj₂ hij₂
      linarith

lemma orderOf_congr {x y g : ℕ → ℝ} (hxy : ∀ n : ℕ, 1 ≤ n → x n = y n) :
    OrderOf x g ↔ OrderOf y g := by
  constructor <;> rintro ⟨c, C, hc, hC, N, hN⟩ <;> refine ⟨c, C, hc, hC, max N 1, fun n hn => ?_⟩
  · rw [← hxy n (le_trans (le_max_right N 1) hn)]
    exact hN n (le_trans (le_max_left N 1) hn)
  · rw [hxy n (le_trans (le_max_right N 1) hn)]
    exact hN n (le_trans (le_max_left N 1) hn)

lemma cost_congr {a : ℝ} {x y : ℕ → ℝ} (hxy : ∀ n : ℕ, 1 ≤ n → x n = y n)
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    (x (i + j) = cost a x i j ↔ y (i + j) = cost a y i j) := by
  simp only [cost, hxy (i + j) (by omega), hxy i hi, hxy j hj]

lemma cost_comm (a : ℝ) (x : ℕ → ℝ) (i j : ℕ) : cost a x i j = cost a x j i := by
  simp only [cost]
  ring

lemma orderOf_rpow_lt_absurd {x : ℕ → ℝ} {r₁ r₂ : ℝ} (h : r₁ < r₂)
    (h1 : OrderOf x (fun n => (n : ℝ) ^ r₁))
    (h2 : OrderOf x (fun n => (n : ℝ) ^ r₂)) : False := by
  obtain ⟨c₁, C₁, hc₁, hC₁, N₁, hN₁⟩ := h1
  obtain ⟨c₂, C₂, hc₂, hC₂, N₂, hN₂⟩ := h2
  have h_tend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (r₂ - r₁)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr h)).comp tendsto_natCast_atTop_atTop
  rw [Filter.tendsto_atTop_atTop] at h_tend
  obtain ⟨N₃, hN₃⟩ := h_tend (C₁ / c₂ + 1)
  let n := max (max N₁ N₂) (max N₃ 1)
  have hn1 : N₁ ≤ n := le_trans (le_max_left N₁ N₂) (le_max_left _ _)
  have hn2 : N₂ ≤ n := le_trans (le_max_right N₁ N₂) (le_max_left _ _)
  have hn3 : N₃ ≤ n := le_trans (le_max_left N₃ 1) (le_max_right _ _)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 1 ≤ n := le_trans (le_max_right N₃ 1) (le_max_right _ _)
    exact_mod_cast this
  have hlt1 : x n < C₁ * (n : ℝ) ^ r₁ := (hN₁ n hn1).2
  have hlt2 : c₂ * (n : ℝ) ^ r₂ < x n := (hN₂ n hn2).1
  have hlt : c₂ * (n : ℝ) ^ r₂ < C₁ * (n : ℝ) ^ r₁ := lt_trans hlt2 hlt1
  have hrpow : (n : ℝ) ^ r₂ = (n : ℝ) ^ r₁ * (n : ℝ) ^ (r₂ - r₁) := by
    rw [← Real.rpow_add hn_pos]
    congr 1
    ring
  rw [hrpow] at hlt
  have hpos_r1 : 0 < (n : ℝ) ^ r₁ := Real.rpow_pos_of_pos hn_pos r₁
  have hbound : (n : ℝ) ^ (r₂ - r₁) < C₁ / c₂ := by
    rw [lt_div_iff₀ hc₂]
    have hmul : (n : ℝ) ^ r₁ * ((n : ℝ) ^ (r₂ - r₁) * c₂) < (n : ℝ) ^ r₁ * C₁ := by
      linarith
    exact lt_of_mul_lt_mul_left hmul hpos_r1.le
  have hge := hN₃ n hn3
  linarith

lemma orderOf_rpow_unique {x : ℕ → ℝ} {r₁ r₂ : ℝ}
    (h1 : OrderOf x (fun n => (n : ℝ) ^ r₁))
    (h2 : OrderOf x (fun n => (n : ℝ) ^ r₂)) : r₁ = r₂ := by
  rcases lt_trichotomy r₁ r₂ with h | h | h
  · exact False.elim (orderOf_rpow_lt_absurd h h1 h2)
  · exact h
  · exact False.elim (orderOf_rpow_lt_absurd h h2 h1)

lemma not_orderOf_rpow_of_sq_log {x : ℕ → ℝ} {r : ℝ} (_hr : 0 < r)
    (hlog : OrderOf x (fun n => (n : ℝ) ^ 2 * Real.log n))
    (hrpow : OrderOf x (fun n => (n : ℝ) ^ r)) : False := by
  obtain ⟨c₁, C₁, hc₁, hC₁, N₁, hN₁⟩ := hlog
  obtain ⟨c₂, C₂, hc₂, hC₂, N₂, hN₂⟩ := hrpow
  by_cases hr2 : r ≤ 2
  · have h_tend : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    rw [Filter.tendsto_atTop_atTop] at h_tend
    obtain ⟨N₃, hN₃⟩ := h_tend (C₂ / c₁ + 1)
    let n := max (max N₁ N₂) (max N₃ 2)
    have hn1 : N₁ ≤ n := le_trans (le_max_left N₁ N₂) (le_max_left _ _)
    have hn2 : N₂ ≤ n := le_trans (le_max_right N₁ N₂) (le_max_left _ _)
    have hn3 : N₃ ≤ n := le_trans (le_max_left N₃ 2) (le_max_right _ _)
    have hn_ge2 : 2 ≤ n := le_trans (le_max_right N₃ 2) (le_max_right _ _)
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (by decide : 1 ≤ 2) hn_ge2
    have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
    have h1 : c₁ * ((n : ℝ) ^ 2 * Real.log n) < x n := (hN₁ n hn1).1
    have h2 : x n < C₂ * (n : ℝ) ^ r := (hN₂ n hn2).2
    have hle : (n : ℝ) ^ r ≤ (n : ℝ) ^ 2 := by
      have hle' := Real.rpow_le_rpow_of_exponent_le hn_ge1 hr2
      simpa using hle'
    have h3 : C₂ * (n : ℝ) ^ r ≤ C₂ * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hle hC₂.le
    have h4 : c₁ * (n : ℝ) ^ 2 * Real.log n < C₂ * (n : ℝ) ^ 2 := by linarith
    have hsq_pos : 0 < c₁ * (n : ℝ) ^ 2 := mul_pos hc₁ (sq_pos_of_pos hn_pos)
    have hlog_lt : Real.log n < C₂ / c₁ := by
      rw [lt_div_iff₀ hc₁]
      have hmul : (n : ℝ) ^ 2 * (Real.log n * c₁) < (n : ℝ) ^ 2 * C₂ := by linarith
      exact lt_of_mul_lt_mul_left hmul (sq_pos_of_pos hn_pos).le
    have hge := hN₃ n hn3
    linarith
  · push Not at hr2
    let δ := (r - 2) / 2
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    have hδ_rem : 0 < r - (2 + δ) := by dsimp [δ]; linarith
    have h_tend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (r - (2 + δ))) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hδ_rem).comp tendsto_natCast_atTop_atTop
    rw [Filter.tendsto_atTop_atTop] at h_tend
    obtain ⟨N₃, hN₃⟩ := h_tend (C₁ / (δ * c₂) + 1)
    let n := max (max N₁ N₂) (max N₃ 2)
    have hn1 : N₁ ≤ n := le_trans (le_max_left N₁ N₂) (le_max_left _ _)
    have hn2 : N₂ ≤ n := le_trans (le_max_right N₁ N₂) (le_max_left _ _)
    have hn3 : N₃ ≤ n := le_trans (le_max_left N₃ 2) (le_max_right _ _)
    have hn_ge2 : 2 ≤ n := le_trans (le_max_right N₃ 2) (le_max_right _ _)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hn_ge2
    have h1 : c₂ * (n : ℝ) ^ r < x n := (hN₂ n hn2).1
    have h2 : x n < C₁ * ((n : ℝ) ^ 2 * Real.log n) := (hN₁ n hn1).2
    have hlog_bound : Real.log n ≤ (n : ℝ) ^ δ / δ := by
      have hpow_pos : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos hn_pos δ
      have hle1 : Real.log ((n : ℝ) ^ δ) ≤ (n : ℝ) ^ δ - 1 := Real.log_le_sub_one_of_pos hpow_pos
      rw [Real.log_rpow hn_pos δ] at hle1
      rw [le_div_iff₀' hδ_pos]
      linarith
    have hpow_add : (n : ℝ) ^ 2 * (n : ℝ) ^ δ = (n : ℝ) ^ (2 + δ) := by
      have h := Real.rpow_add hn_pos 2 δ
      simpa using h.symm
    have h3 : C₁ * ((n : ℝ) ^ 2 * Real.log n) ≤ (C₁ / δ) * (n : ℝ) ^ (2 + δ) := by
      have hmul : (n : ℝ) ^ 2 * Real.log n ≤ (n : ℝ) ^ 2 * ((n : ℝ) ^ δ / δ) :=
        mul_le_mul_of_nonneg_left hlog_bound (sq_nonneg (n : ℝ))
      have heq : (n : ℝ) ^ 2 * ((n : ℝ) ^ δ / δ) = (n : ℝ) ^ (2 + δ) / δ := by
        rw [← hpow_add]
        ring
      rw [heq] at hmul
      calc C₁ * ((n : ℝ) ^ 2 * Real.log n)
          ≤ C₁ * ((n : ℝ) ^ (2 + δ) / δ) := mul_le_mul_of_nonneg_left hmul hC₁.le
        _ = (C₁ / δ) * (n : ℝ) ^ (2 + δ) := by ring
    have h4 : c₂ * (n : ℝ) ^ r < (C₁ / δ) * (n : ℝ) ^ (2 + δ) := by linarith
    have hpow_split : (n : ℝ) ^ r = (n : ℝ) ^ (2 + δ) * (n : ℝ) ^ (r - (2 + δ)) := by
      rw [← Real.rpow_add hn_pos]
      congr 1
      ring
    rw [hpow_split] at h4
    have hpos_2d : 0 < (n : ℝ) ^ (2 + δ) := Real.rpow_pos_of_pos hn_pos (2 + δ)
    have hbound : (n : ℝ) ^ (r - (2 + δ)) < C₁ / (δ * c₂) := by
      rw [lt_div_iff₀ (mul_pos hδ_pos hc₂)]
      have hmul : (n : ℝ) ^ (2 + δ) * (c₂ * (n : ℝ) ^ (r - (2 + δ)) * δ) <
          (n : ℝ) ^ (2 + δ) * C₁ := by
        have h4' : (n : ℝ) ^ (2 + δ) * (c₂ * (n : ℝ) ^ (r - (2 + δ))) <
            (n : ℝ) ^ (2 + δ) * (C₁ / δ) := by linarith
        have h5 := lt_of_mul_lt_mul_left h4' hpos_2d.le
        have h6 : c₂ * (n : ℝ) ^ (r - (2 + δ)) * δ < C₁ := (lt_div_iff₀ hδ_pos).mp h5
        exact mul_lt_mul_of_pos_left h6 hpos_2d
      have h7 := lt_of_mul_lt_mul_left hmul hpos_2d.le
      linarith
    have hge := hN₃ n hn3
    linarith

-- Regime 1: 0 < a < 1
def P_lt (a : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n + 2 => a * P_lt a (n + 1) + 2 * (n + 1 : ℝ)

lemma P_lt_succ (a : ℝ) : ∀ n : ℕ, 1 ≤ n → P_lt a (n + 1) = a * P_lt a n + 2 * (n : ℝ)
  | 0, h => by omega
  | k + 1, _ => by dsimp [P_lt]; push_cast; ring

lemma P_lt_diff (a : ℝ) : ∀ n : ℕ, 1 ≤ n →
    (1 - a) * (P_lt a (n + 1) - P_lt a n) = 2 * (1 - a ^ n) := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hn with h1 | h2
    · have hk : k = 0 := by omega
      subst hk
      simp [P_lt]
      ring
    · have hk : 1 ≤ k := by omega
      have ihk := ih hk
      have h_s1 := P_lt_succ a (k + 1) (by omega)
      have h_s2 := P_lt_succ a k hk
      rw [pow_succ']
      push_cast at h_s1 ⊢
      linear_combination a * ihk + (1 - a) * h_s1 - (1 - a) * h_s2

lemma P_lt_closed (a : ℝ) : ∀ n : ℕ, 1 ≤ n →
    (1 - a) ^ 2 * P_lt a n = 2 * ((n : ℝ) - 1 - (n : ℝ) * a + a ^ n) := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hn with h1 | h2
    · have hk : k = 0 := by omega
      subst hk
      simp [P_lt]
    · have hk : 1 ≤ k := by omega
      have ihk := ih hk
      have hdiff := P_lt_diff a k hk
      push_cast
      linear_combination ihk + (1 - a) * hdiff

lemma one_sub_pow_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ d : ℕ, 1 - a ^ d ≤ (1 - a) * (d : ℝ) := by
  intro d
  induction d with
  | zero => simp
  | succ k ih =>
    have hpow : a ^ k ≤ 1 := pow_le_one₀ ha0.le ha1.le
    have h1a : 0 ≤ 1 - a := by linarith
    rw [pow_succ']
    push_cast
    nlinarith

lemma cost_lt_step {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i + 2 ≤ j) :
    cost a (P_lt a) i j < cost a (P_lt a) (i + 1) (j - 1) := by
  have hj1 : 1 ≤ j - 1 := by omega
  have hd1 : (1 - a) * (P_lt a (i + 1) - P_lt a i) = 2 * (1 - a ^ i) := P_lt_diff a i hi
  have hd2 : (1 - a) * (P_lt a j - P_lt a (j - 1)) = 2 * (1 - a ^ (j - 1)) := by
    have h := P_lt_diff a (j - 1) hj1
    rwa [Nat.sub_add_cancel (by omega)] at h
  have h1a : 0 < 1 - a := by linarith
  have hdiff_mul : (1 - a) * (cost a (P_lt a) (i + 1) (j - 1) - cost a (P_lt a) i j) =
      2 * ((1 - a) * ((j - 1 - i : ℕ) : ℝ) - a ^ (i + 1) * (1 - a ^ (j - 1 - i))) := by
    have hj_eq : j = (i + 1) + (j - 1 - i) := by omega
    have hj_cast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      have : 1 ≤ j := by omega
      rw [Nat.cast_sub this, Nat.cast_one]
    have hji_cast : ((j - 1 - i : ℕ) : ℝ) = (j : ℝ) - 1 - (i : ℝ) := by
      rw [Nat.cast_sub (by omega), hj_cast]
    simp only [cost]
    rw [hj_cast, hji_cast]
    push_cast
    have hpow_j : a ^ j = a ^ (i + 1) * a ^ (j - 1 - i) := by
      conv_lhs => rw [hj_eq, pow_add]
    have hpow_jm1 : a * a ^ (j - 1) = a ^ j := by
      rw [← pow_succ']
      congr 1
      omega
    linear_combination a * hd1 - a * hd2 + 2 * hpow_j + 2 * hpow_jm1
  have hle_d : 1 - a ^ (j - 1 - i) ≤ (1 - a) * ((j - 1 - i : ℕ) : ℝ) :=
    one_sub_pow_le ha0 ha1 (j - 1 - i)
  have hpow_lt1 : a ^ (i + 1) < 1 := pow_lt_one₀ ha0.le ha1 (by omega)
  have hpow_pos : 0 < 1 - a ^ (j - 1 - i) := by
    have : a ^ (j - 1 - i) < 1 := pow_lt_one₀ ha0.le ha1 (by omega)
    linarith
  have hstrict : a ^ (i + 1) * (1 - a ^ (j - 1 - i)) < (1 - a) * ((j - 1 - i : ℕ) : ℝ) := by
    have h1 : a ^ (i + 1) * (1 - a ^ (j - 1 - i)) < 1 * (1 - a ^ (j - 1 - i)) :=
      mul_lt_mul_of_pos_right hpow_lt1 hpow_pos
    linarith
  have hpos : 0 < (1 - a) * (cost a (P_lt a) (i + 1) (j - 1) - cost a (P_lt a) i j) := by
    rw [hdiff_mul]
    linarith
  have hpos' : 0 < cost a (P_lt a) (i + 1) (j - 1) - cost a (P_lt a) i j :=
    (mul_pos_iff_of_pos_left h1a).mp hpos
  linarith

lemma P_lt_min_aux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      P_lt a (i + j) ≤ cost a (P_lt a) i j ∧
      (P_lt a (i + j) = cost a (P_lt a) i j ↔ i = 1 ∨ j = 1) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro j hi hj
    rcases eq_or_lt_of_le hi with rfl | hi2
    · have h1 : cost a (P_lt a) 1 j = P_lt a (1 + j) := by
        rw [Nat.add_comm 1 j, P_lt_succ a j hj]
        simp [cost, P_lt]
      rw [h1]
      exact ⟨le_rfl, ⟨fun _ => Or.inl rfl, fun _ => rfl⟩⟩
    · rcases eq_or_lt_of_le hj with rfl | hj2
      · have h1 : cost a (P_lt a) i 1 = P_lt a (i + 1) := by
          rw [P_lt_succ a i hi]
          simp [cost, P_lt]
        rw [h1]
        exact ⟨le_rfl, ⟨fun _ => Or.inr rfl, fun _ => rfl⟩⟩
      · have hlt : P_lt a (i + j) < cost a (P_lt a) i j := by
          by_cases hij : i ≤ j
          · have hstep := cost_lt_step ha0 ha1 (by omega : 1 ≤ i - 1) (by omega : (i - 1) + 2 ≤ j + 1)
            have hsub : (i - 1) + 1 = i := by omega
            have hsub2 : (j + 1) - 1 = j := by omega
            rw [hsub, hsub2] at hstep
            have hih := (ih (i - 1) (by omega) (j + 1) (by omega) (by omega)).1
            have hsum : (i - 1) + (j + 1) = i + j := by omega
            rw [hsum] at hih
            linarith
          · have hij' : j < i := by omega
            rw [cost_comm]
            have hstep := cost_lt_step ha0 ha1 (by omega : 1 ≤ j - 1) (by omega : (j - 1) + 2 ≤ i + 1)
            have hsub : (j - 1) + 1 = j := by omega
            have hsub2 : (i + 1) - 1 = i := by omega
            rw [hsub, hsub2] at hstep
            have hih := (ih (j - 1) (by omega) (i + 1) (by omega) (by omega)).1
            have hsum : (j - 1) + (i + 1) = i + j := by omega
            rw [hsum] at hih
            linarith
        refine ⟨hlt.le, ?_⟩
        constructor
        · intro h
          linarith
        · rintro (rfl | rfl) <;> omega

lemma P_lt_recurs {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : Recurs a (P_lt a) := by
  refine ⟨rfl, fun n hn => ⟨?_, ?_⟩⟩
  · intro i j hi hj hij
    rw [← hij]
    exact (P_lt_min_aux ha0 ha1 i j hi hj).1
  · refine ⟨1, n - 1, by omega, by omega, by omega, ?_⟩
    have h := (P_lt_min_aux ha0 ha1 1 (n - 1) (by omega) (by omega)).2.mpr (Or.inl rfl)
    rwa [show 1 + (n - 1) = n by omega] at h

lemma P_lt_orderOf {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    OrderOf (P_lt a) (fun n => (n : ℝ) ^ (1 : ℝ)) := by
  have h1a : 0 < 1 - a := by linarith
  refine ⟨1 / (1 - a), 3 / (1 - a), div_pos one_pos h1a, div_pos (by norm_num) h1a,
    Nat.ceil (2 / (1 - a)) + 2, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hclosed := P_lt_closed a n hn1
  have hn_ge : 2 / (1 - a) ≤ (n : ℝ) := by
    have hceil : 2 / (1 - a) ≤ (Nat.ceil (2 / (1 - a)) : ℝ) := Nat.le_ceil _
    have hle : (Nat.ceil (2 / (1 - a)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : Nat.ceil (2 / (1 - a)) ≤ n)
    linarith
  have h1an : 2 ≤ (1 - a) * (n : ℝ) := (div_le_iff₀' h1a).mp hn_ge
  have hpow_pos : 0 < a ^ n := pow_pos ha0 n
  have hpow_le : a ^ n ≤ 1 := pow_le_one₀ ha0.le ha1.le
  have h_eq : (1 - a) ^ 2 * P_lt a n = 2 * ((1 - a) * (n : ℝ) - 1 + a ^ n) := by
    rw [hclosed]
    ring
  have hlow : (1 - a) * (n : ℝ) < (1 - a) ^ 2 * P_lt a n := by linarith
  have hhigh : (1 - a) ^ 2 * P_lt a n < 3 * (1 - a) * (n : ℝ) := by linarith
  have h1a2 : 0 < (1 - a) ^ 2 := sq_pos_of_pos h1a
  dsimp only
  rw [Real.rpow_one]
  constructor
  · rw [div_mul_eq_mul_div, div_lt_iff₀ h1a]
    have hmul : (1 - a) * (1 * (n : ℝ)) < (1 - a) * (P_lt a n * (1 - a)) := by
      calc (1 - a) * (1 * (n : ℝ)) = (1 - a) * (n : ℝ) := by ring
        _ < (1 - a) ^ 2 * P_lt a n := hlow
        _ = (1 - a) * (P_lt a n * (1 - a)) := by ring
    exact lt_of_mul_lt_mul_left hmul h1a.le
  · rw [div_mul_eq_mul_div, lt_div_iff₀ h1a]
    have hmul : (1 - a) * (P_lt a n * (1 - a)) < (1 - a) * (3 * (n : ℝ)) := by
      calc (1 - a) * (P_lt a n * (1 - a)) = (1 - a) ^ 2 * P_lt a n := by ring
        _ < 3 * (1 - a) * (n : ℝ) := hhigh
        _ = (1 - a) * (3 * (n : ℝ)) := by ring
    exact lt_of_mul_lt_mul_left hmul h1a.le

-- Regime 2: a = 1
def P_eq (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) - 1)

lemma P_eq_cost (i j : ℕ) : cost 1 P_eq i j = P_eq (i + j) := by
  simp only [cost, P_eq]
  push_cast
  ring

lemma P_eq_recurs : Recurs 1 P_eq := by
  refine ⟨by simp [P_eq], fun n hn => ⟨?_, ?_⟩⟩
  · intro i j _ _ hij
    rw [← hij, P_eq_cost]
  · exact ⟨1, n - 1, by omega, by omega, by omega, by rw [P_eq_cost, show 1 + (n - 1) = n by omega]⟩

lemma P_eq_orderOf : OrderOf P_eq (fun n => (n : ℝ) ^ (2 : ℝ)) := by
  refine ⟨1 / 3, 2, by norm_num, by norm_num, 2, fun n hn => ?_⟩
  have hn_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hrpow : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := Real.rpow_two (n : ℝ)
  dsimp only
  rw [hrpow]
  simp only [P_eq]
  constructor
  · nlinarith
  · nlinarith

-- Regime 3: 1 < a
def P_gt (a : ℝ) (n : ℕ) : ℝ :=
  if h : n < 2 then 0
  else a * (P_gt a (n / 2) + P_gt a (n - n / 2)) + 2 * (n / 2 : ℕ) * (n - n / 2 : ℕ)
termination_by n
decreasing_by all_goals omega

lemma P_gt_one (a : ℝ) : P_gt a 1 = 0 := by
  rw [P_gt]
  simp

lemma P_gt_even (a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    P_gt a (2 * k) = 2 * a * P_gt a k + 2 * (k : ℝ) ^ 2 := by
  rw [P_gt]
  have hnot : ¬ (2 * k < 2) := by omega
  have h1 : (2 * k) / 2 = k := by omega
  have h2 : 2 * k - k = k := by omega
  simp only [hnot, ↓reduceDIte, h1, h2]
  ring

lemma P_gt_odd (a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    P_gt a (2 * k + 1) = a * (P_gt a k + P_gt a (k + 1)) + 2 * (k : ℝ) * ((k : ℝ) + 1) := by
  rw [P_gt]
  have hnot : ¬ (2 * k + 1 < 2) := by omega
  have h1 : (2 * k + 1) / 2 = k := by omega
  have h2 : 2 * k + 1 - k = k + 1 := by omega
  simp only [hnot, ↓reduceDIte, h1, h2]
  push_cast
  ring

lemma P_gt_convex {a : ℝ} (ha : 1 < a) : ∀ n : ℕ, 2 ≤ n →
    2 ≤ P_gt a (n + 1) - 2 * P_gt a n + P_gt a (n - 1) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      have hk1 : 1 ≤ k := by omega
      rcases eq_or_lt_of_le hk1 with rfl | hk2
      · rw [show 1 + 1 + 1 = 2 * 1 + 1 by rfl, show 1 + 1 = 2 * 1 by rfl,
          show 2 * 1 - 1 = 1 by rfl, P_gt_odd a (by omega), P_gt_even a (by omega), P_gt_one]
        have h2 : P_gt a 2 = 2 := by
          rw [show (2 : ℕ) = 2 * 1 by rfl, P_gt_even a (by omega), P_gt_one]
          norm_num
        rw [h2]
        push_cast
        linarith
      · have hk_ge2 : 2 ≤ k := by omega
        have heq1 : k + k + 1 = 2 * k + 1 := by omega
        have heq2 : k + k = 2 * k := by omega
        have heq3 : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
        rw [heq1, heq2, heq3, P_gt_odd a hk1, P_gt_even a hk1, P_gt_odd a (by omega : 1 ≤ k - 1)]
        have hkm1 : k - 1 + 1 = k := by omega
        rw [hkm1]
        have hih := ih k (by omega) hk_ge2
        have hmul : a * (P_gt a (k + 1) - 2 * P_gt a k + P_gt a (k - 1)) ≥ a * 2 :=
          mul_le_mul_of_nonneg_left hih (by linarith)
        have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub hk1, Nat.cast_one]
        rw [hcast] at *
        have halg : a * (P_gt a k + P_gt a (k + 1)) + 2 * (k : ℝ) * ((k : ℝ) + 1) -
            2 * (2 * a * P_gt a k + 2 * (k : ℝ) ^ 2) +
            (a * (P_gt a (k - 1) + P_gt a k) + 2 * ((k : ℝ) - 1) * (((k : ℝ) - 1) + 1)) =
            a * (P_gt a (k + 1) - 2 * P_gt a k + P_gt a (k - 1)) := by ring
        rw [halg]
        linarith
    · subst hk
      have hk1 : 1 ≤ k := by omega
      have heq1 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      have heq2 : 2 * k + 1 - 1 = 2 * k := by omega
      rw [heq1, heq2, P_gt_even a (by omega : 1 ≤ k + 1), P_gt_odd a hk1, P_gt_even a hk1]
      push_cast
      linarith

lemma P_gt_diff_ge2 {a : ℝ} (ha : 1 < a) : ∀ n : ℕ, 1 ≤ n →
    2 ≤ P_gt a (n + 1) - P_gt a n := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hn with h1 | h2
    · have hk : k = 0 := by omega
      subst hk
      rw [show 0 + 1 + 1 = 2 * 1 by rfl, P_gt_even a (by omega), P_gt_one]
      norm_num
    · have hih := ih (by omega)
      have hconv := P_gt_convex ha (k + 1) (by omega)
      have hsub : k + 1 - 1 = k := by omega
      rw [hsub] at hconv
      linarith

lemma P_gt_mono {a : ℝ} (ha : 1 < a) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    P_gt a m ≤ P_gt a n := by
  induction hmn with
  | refl => exact le_rfl
  | step h ih =>
    have hdiff := P_gt_diff_ge2 ha _ (le_trans hm h)
    linarith

lemma P_gt_diff_telescope {a : ℝ} (ha : 1 < a) {i : ℕ} (hi : 1 ≤ i) :
    ∀ d : ℕ, 1 ≤ d →
      2 * (d : ℝ) ≤ (P_gt a (i + 1 + d) - P_gt a (i + d)) - (P_gt a (i + 1) - P_gt a i) := by
  intro d hd
  induction d with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hd with h1 | h2
    · have hk : k = 0 := by omega
      subst hk
      have hconv := P_gt_convex ha (i + 1) (by omega)
      have hsub : i + 1 - 1 = i := by omega
      rw [hsub] at hconv
      rw [show i + 1 + (0 + 1) = i + 1 + 1 by omega, show i + (0 + 1) = i + 1 by omega]
      push_cast
      linarith
    · have hih := ih (by omega)
      have hconv := P_gt_convex ha (i + k + 1) (by omega)
      have hsub : i + k + 1 - 1 = i + k := by omega
      rw [hsub] at hconv
      have heq1 : i + 1 + (k + 1) = i + k + 1 + 1 := by omega
      have heq2 : i + (k + 1) = i + k + 1 := by omega
      have hcomm : i + 1 + k = i + k + 1 := by omega
      rw [hcomm] at hih
      rw [heq1, heq2]
      push_cast
      linarith

lemma cost_gt_step {a : ℝ} (ha : 1 < a) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) :
    cost a (P_gt a) (i + 1) (j - 1) < cost a (P_gt a) i j := by
  let d := j - 1 - i
  have hd : 1 ≤ d := by omega
  have hj1 : i + d = j - 1 := by omega
  have hj2 : i + 1 + d = j := by omega
  have htel := P_gt_diff_telescope ha hi d hd
  rw [hj1, hj2] at htel
  have hj_cast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hd_cast : (d : ℝ) = (j : ℝ) - 1 - (i : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub (by omega), hj_cast]
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmul : a * (2 * (d : ℝ)) ≤
      a * ((P_gt a j - P_gt a (j - 1)) - (P_gt a (i + 1) - P_gt a i)) :=
    mul_le_mul_of_nonneg_left htel (by linarith)
  have hdiff : cost a (P_gt a) (i + 1) (j - 1) - cost a (P_gt a) i j =
      2 * (d : ℝ) - a * ((P_gt a j - P_gt a (j - 1)) - (P_gt a (i + 1) - P_gt a i)) := by
    simp only [cost]
    rw [hj_cast, hd_cast]
    push_cast
    ring
  have hlt : 2 * (d : ℝ) - a * (2 * (d : ℝ)) < 0 := by
    have : 2 * (d : ℝ) * (1 - a) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  linarith

lemma P_gt_balanced {a : ℝ} {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h1 : i ≤ j + 1) (h2 : j ≤ i + 1) :
    cost a (P_gt a) i j = P_gt a (i + j) := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hj_eq : j = i + 1 := by omega
    subst hj_eq
    rw [show i + (i + 1) = 2 * i + 1 by omega, P_gt_odd a hi]
    simp only [cost]
    push_cast
    ring
  · rw [show i + i = 2 * i by omega, P_gt_even a hi]
    simp only [cost]
    ring
  · have hi_eq : i = j + 1 := by omega
    subst hi_eq
    rw [cost_comm, show j + 1 + j = 2 * j + 1 by omega, P_gt_odd a hj]
    simp only [cost]
    push_cast
    ring

lemma P_gt_min_aux {a : ℝ} (ha : 1 < a) :
    ∀ d i j : ℕ, 1 ≤ i → 1 ≤ j → (j - i) + (i - j) = d →
      P_gt a (i + j) ≤ cost a (P_gt a) i j ∧
      (P_gt a (i + j) = cost a (P_gt a) i j ↔ i ≤ j + 1 ∧ j ≤ i + 1) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i j hi hj hd
    by_cases hbal : i ≤ j + 1 ∧ j ≤ i + 1
    · have heq := P_gt_balanced (a := a) hi hj hbal.1 hbal.2
      rw [heq]
      exact ⟨le_rfl, ⟨fun _ => hbal, fun _ => rfl⟩⟩
    · have hlt : P_gt a (i + j) < cost a (P_gt a) i j := by
        by_cases hij : i + 2 ≤ j
        · have hstep := cost_gt_step ha hi hij
          have hd' : (j - 1 - (i + 1)) + ((i + 1) - (j - 1)) < d := by omega
          have hih := (ih _ hd' (i + 1) (j - 1) (by omega) (by omega) rfl).1
          have hsum : (i + 1) + (j - 1) = i + j := by omega
          rw [hsum] at hih
          linarith
        · have hji : j + 2 ≤ i := by omega
          rw [cost_comm]
          have hstep := cost_gt_step ha hj hji
          have hd' : (i - 1 - (j + 1)) + ((j + 1) - (i - 1)) < d := by omega
          have hih := (ih _ hd' (j + 1) (i - 1) (by omega) (by omega) rfl).1
          have hsum : (j + 1) + (i - 1) = i + j := by omega
          rw [hsum] at hih
          linarith
      refine ⟨hlt.le, ⟨fun h => by linarith, fun h => absurd h hbal⟩⟩

lemma P_gt_recurs {a : ℝ} (ha : 1 < a) : Recurs a (P_gt a) := by
  refine ⟨by rw [P_gt]; simp, fun n hn => ⟨?_, ?_⟩⟩
  · intro i j hi hj hij
    rw [← hij]
    exact (P_gt_min_aux ha _ i j hi hj rfl).1
  · refine ⟨n / 2, n - n / 2, by omega, by omega, by omega, ?_⟩
    have hbal1 : n / 2 ≤ (n - n / 2) + 1 := by omega
    have hbal2 : n - n / 2 ≤ n / 2 + 1 := by omega
    have h := P_gt_balanced (a := a) (by omega : 1 ≤ n / 2) (by omega : 1 ≤ n - n / 2) hbal1 hbal2
    rw [show n / 2 + (n - n / 2) = n by omega] at h
    exact h.symm

lemma P_gt_pow2_eq2 : ∀ m : ℕ, P_gt 2 (2 ^ m) = (1 / 2 : ℝ) * (m : ℝ) * ((2 ^ m : ℕ) : ℝ) ^ 2 := by
  intro m
  induction m with
  | zero => simp [P_gt_one]
  | succ k ih =>
    have hk : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hpow, P_gt_even 2 hk, ih]
    push_cast
    ring

lemma pow2_sq_eq_pow4 (m : ℕ) : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
  calc ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ m * (2 : ℝ) ^ m := by ring
    _ = ((2 : ℝ) * 2) ^ m := by rw [← mul_pow]
    _ = (4 : ℝ) ^ m := by norm_num

lemma P_gt_pow2_ne2 (a : ℝ) : ∀ m : ℕ, (2 - a) * P_gt a (2 ^ m) = (4 : ℝ) ^ m - (2 * a) ^ m := by
  intro m
  induction m with
  | zero => simp [P_gt_one]
  | succ k ih =>
    have hk : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [hpow, P_gt_even a hk]
    have h4 : ((2 ^ k : ℕ) : ℝ) ^ 2 = (4 : ℝ) ^ k := by
      push_cast
      exact pow2_sq_eq_pow4 k
    rw [h4]
    calc (2 - a) * (2 * a * P_gt a (2 ^ k) + 2 * (4 : ℝ) ^ k)
        = 2 * a * ((2 - a) * P_gt a (2 ^ k)) + 2 * (2 - a) * (4 : ℝ) ^ k := by ring
      _ = 2 * a * ((4 : ℝ) ^ k - (2 * a) ^ k) + 2 * (2 - a) * (4 : ℝ) ^ k := by rw [ih]
      _ = (4 : ℝ) ^ (k + 1) - (2 * a) ^ (k + 1) := by ring

lemma pow_sub_pow_ge {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    ∀ m : ℕ, 1 ≤ m → (x - y) * x ^ (m - 1) ≤ x ^ m - y ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hm with h1 | h2
    · have hk : k = 0 := by omega
      subst hk
      simp
    · have hk : 1 ≤ k := by omega
      have hih := ih hk
      have hsub : k + 1 - 1 = k := by omega
      have hsub2 : k - 1 + 1 = k := by omega
      rw [hsub]
      have hx0 : 0 ≤ x := le_trans hy hxy
      have hyk : 0 ≤ y ^ k := pow_nonneg hy k
      have h1 : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + y ^ k * (x - y) := by ring
      rw [h1]
      have h2' : x * ((x - y) * x ^ (k - 1)) ≤ x * (x ^ k - y ^ k) := mul_le_mul_of_nonneg_left hih hx0
      have h3 : x * ((x - y) * x ^ (k - 1)) = (x - y) * x ^ k := by
        rw [← mul_assoc, mul_comm x (x - y), mul_assoc, ← pow_succ', hsub2]
      rw [h3] at h2'
      nlinarith

lemma P_gt_orderOf_lt2 {a : ℝ} (ha1 : 1 < a) (ha2 : a < 2) :
    OrderOf (P_gt a) (fun n => (n : ℝ) ^ (2 : ℝ)) := by
  have h2a : 0 < 2 - a := by linarith
  refine ⟨1 / 8, 5 / (2 - a), by norm_num, div_pos (by norm_num) h2a, 2, fun n hn => ?_⟩
  let m := Nat.log 2 n
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact Nat.le_log_of_pow_le (by decide) hn
  have hpow_le : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hlt_pow : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hm_pow_ge1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have hmono1 : P_gt a (2 ^ m) ≤ P_gt a n := P_gt_mono ha1 hm_pow_ge1 hpow_le
  have hmono2 : P_gt a n ≤ P_gt a (2 ^ (m + 1)) := P_gt_mono ha1 (by omega) (le_of_lt hlt_pow)
  have hne2_m := P_gt_pow2_ne2 a m
  have hne2_m1 := P_gt_pow2_ne2 a (m + 1)
  have hdiff_ge : (2 - a) * (2 : ℝ) ^ (m - 1) ≤ (2 : ℝ) ^ m - a ^ m :=
    pow_sub_pow_ge (by linarith) ha2.le m hm1
  have h4m_ge : (1 / 2 : ℝ) * (2 - a) * (4 : ℝ) ^ m ≤ (4 : ℝ) ^ m - (2 * a) ^ m := by
    have heq1 : (4 : ℝ) ^ m - (2 * a) ^ m = (2 : ℝ) ^ m * ((2 : ℝ) ^ m - a ^ m) := by
      rw [← pow2_sq_eq_pow4 m, mul_pow]
      ring
    have heq2 : (2 : ℝ) ^ m * ((2 - a) * (2 : ℝ) ^ (m - 1)) = (1 / 2 : ℝ) * (2 - a) * (4 : ℝ) ^ m := by
      have h2m : (2 : ℝ) * (2 : ℝ) ^ (m - 1) = (2 : ℝ) ^ m := by
        rw [← pow_succ', Nat.sub_add_cancel hm1]
      calc (2 : ℝ) ^ m * ((2 - a) * (2 : ℝ) ^ (m - 1))
          = (1 / 2 : ℝ) * (2 - a) * ((2 : ℝ) ^ m * ((2 : ℝ) * (2 : ℝ) ^ (m - 1))) := by ring
        _ = (1 / 2 : ℝ) * (2 - a) * ((2 : ℝ) ^ m * (2 : ℝ) ^ m) := by rw [h2m]
        _ = (1 / 2 : ℝ) * (2 - a) * (4 : ℝ) ^ m := by rw [← pow2_sq_eq_pow4 m]; ring
    rw [heq1, ← heq2]
    exact mul_le_mul_of_nonneg_left hdiff_ge (pow_nonneg (by norm_num) m)
  have hlow_2m : (1 / 2 : ℝ) * (4 : ℝ) ^ m ≤ P_gt a (2 ^ m) := by
    rw [← hne2_m] at h4m_ge
    nlinarith
  have hhigh_2m1 : P_gt a (2 ^ (m + 1)) ≤ (4 / (2 - a)) * (4 : ℝ) ^ m := by
    have hpow_nn : 0 ≤ (2 * a) ^ (m + 1) := pow_nonneg (by linarith) (m + 1)
    have hle : (2 - a) * P_gt a (2 ^ (m + 1)) ≤ 4 * (4 : ℝ) ^ m := by
      rw [hne2_m1]
      have : (4 : ℝ) ^ (m + 1) = 4 * (4 : ℝ) ^ m := by ring
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀' h2a]
    linarith
  have hn_lt : (n : ℝ) < 2 * (2 : ℝ) ^ m := by
    have : (n : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hlt_pow
    push_cast at this
    rw [pow_succ'] at this
    linarith
  have hn_ge : (2 : ℝ) ^ m ≤ (n : ℝ) := by exact_mod_cast hpow_le
  have hrpow : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := Real.rpow_two (n : ℝ)
  dsimp only
  rw [hrpow]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnsq_pos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_pos
  constructor
  · have hnsq_lt : (n : ℝ) ^ 2 < 4 * (4 : ℝ) ^ m := by
      calc (n : ℝ) ^ 2 < (2 * (2 : ℝ) ^ m) ^ 2 := sq_lt_sq' (by linarith) hn_lt
        _ = 4 * ((2 : ℝ) ^ m) ^ 2 := by ring
        _ = 4 * (4 : ℝ) ^ m := by rw [pow2_sq_eq_pow4 m]
    linarith
  · have h4m_le : (4 : ℝ) ^ m ≤ (n : ℝ) ^ 2 := by
      calc (4 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 2 := (pow2_sq_eq_pow4 m).symm
        _ ≤ (n : ℝ) ^ 2 := sq_le_sq' (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m]) hn_ge
    have hle : P_gt a n ≤ (4 / (2 - a)) * (n : ℝ) ^ 2 := by
      calc P_gt a n ≤ P_gt a (2 ^ (m + 1)) := hmono2
        _ ≤ (4 / (2 - a)) * (4 : ℝ) ^ m := hhigh_2m1
        _ ≤ (4 / (2 - a)) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h4m_le (div_nonneg (by norm_num) h2a.le)
    have hlt_5 : 4 / (2 - a) < 5 / (2 - a) := div_lt_div_of_pos_right (by norm_num) h2a
    nlinarith

lemma P_gt_orderOf_eq2 : OrderOf (P_gt 2) (fun n => (n : ℝ) ^ 2 * Real.log n) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / (17 * Real.log 2), 5 / Real.log 2,
    div_pos one_pos (by linarith), div_pos (by norm_num) hlog2_pos, 2, fun n hn => ?_⟩
  let m := Nat.log 2 n
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact Nat.le_log_of_pow_le (by decide) hn
  have hpow_le : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hlt_pow : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hm_pow_ge1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have hmono1 : P_gt 2 (2 ^ m) ≤ P_gt 2 n := P_gt_mono (by norm_num) hm_pow_ge1 hpow_le
  have hmono2 : P_gt 2 n ≤ P_gt 2 (2 ^ (m + 1)) := P_gt_mono (by norm_num) (by omega) (le_of_lt hlt_pow)
  have heq_m := P_gt_pow2_eq2 m
  have heq_m1 := P_gt_pow2_eq2 (m + 1)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hn
  have h2m_pos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hm_pow_ge1
  have h2m1_pos : (0 : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ) := by positivity
  have hlog_le : (m : ℝ) * Real.log 2 ≤ Real.log n := by
    have h1 : Real.log ((2 ^ m : ℕ) : ℝ) ≤ Real.log n :=
      Real.log_le_log h2m_pos (by exact_mod_cast hpow_le)
    rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
  have hlog_lt : Real.log n < ((m + 1 : ℕ) : ℝ) * Real.log 2 := by
    have h1 : Real.log n < Real.log ((2 ^ (m + 1) : ℕ) : ℝ) :=
      Real.log_lt_log hn_pos (by exact_mod_cast hlt_pow)
    rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hm_half : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    push_cast
    linarith
  have hn_lt : (n : ℝ) < 2 * (2 : ℝ) ^ m := by
    have : (n : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hlt_pow
    push_cast at this
    rw [pow_succ'] at this
    linarith
  have hn_ge : (2 : ℝ) ^ m ≤ (n : ℝ) := by
    have : ((2 ^ m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpow_le
    push_cast at this
    exact this
  have hnsq_lt : (n : ℝ) ^ 2 < 4 * (4 : ℝ) ^ m := by
    calc (n : ℝ) ^ 2 < (2 * (2 : ℝ) ^ m) ^ 2 := sq_lt_sq' (by linarith) hn_lt
      _ = 4 * ((2 : ℝ) ^ m) ^ 2 := by ring
      _ = 4 * (4 : ℝ) ^ m := by rw [pow2_sq_eq_pow4 m]
  have h4m_le : (4 : ℝ) ^ m ≤ (n : ℝ) ^ 2 := by
    calc (4 : ℝ) ^ m = ((2 : ℝ) ^ m) ^ 2 := (pow2_sq_eq_pow4 m).symm
      _ ≤ (n : ℝ) ^ 2 := sq_le_sq' (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m]) hn_ge
  have hlog_n_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hn)
  constructor
  · have hlog_lt' : Real.log n < 2 * (m : ℝ) * Real.log 2 := by
      have : ((m + 1 : ℕ) : ℝ) * Real.log 2 ≤ 2 * (m : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hm_half hlog2_pos.le
      linarith
    have hprod : (n : ℝ) ^ 2 * Real.log n < 8 * (m : ℝ) * (4 : ℝ) ^ m * Real.log 2 := by
      calc (n : ℝ) ^ 2 * Real.log n
          < (4 * (4 : ℝ) ^ m) * Real.log n := mul_lt_mul_of_pos_right hnsq_lt hlog_n_pos
        _ < (4 * (4 : ℝ) ^ m) * (2 * (m : ℝ) * Real.log 2) :=
          mul_lt_mul_of_pos_left hlog_lt' (by positivity)
        _ = 8 * (m : ℝ) * (4 : ℝ) ^ m * Real.log 2 := by ring
    have heq_m' : P_gt 2 (2 ^ m) = (1 / 2 : ℝ) * (m : ℝ) * (4 : ℝ) ^ m := by
      rw [heq_m]
      push_cast
      rw [pow2_sq_eq_pow4 m]
    have h16 : (1 / (16 * Real.log 2)) * ((n : ℝ) ^ 2 * Real.log n) < P_gt 2 (2 ^ m) := by
      rw [heq_m']
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      linarith
    have h17 : (1 / (17 * Real.log 2)) < (1 / (16 * Real.log 2)) :=
      div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
    have hlt_17 : (1 / (17 * Real.log 2)) * ((n : ℝ) ^ 2 * Real.log n) <
        (1 / (16 * Real.log 2)) * ((n : ℝ) ^ 2 * Real.log n) :=
      mul_lt_mul_of_pos_right h17 (mul_pos (sq_pos_of_pos hn_pos) hlog_n_pos)
    linarith
  · have h4m1 : ((2 ^ (m + 1) : ℕ) : ℝ) ^ 2 = 4 * (4 : ℝ) ^ m := by
      push_cast
      have h2m1 : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := pow_succ' 2 m
      rw [h2m1]
      calc (2 * (2 : ℝ) ^ m) ^ 2 = 4 * ((2 : ℝ) ^ m) ^ 2 := by ring
        _ = 4 * (4 : ℝ) ^ m := by rw [pow2_sq_eq_pow4 m]
    have heq_m1' : P_gt 2 (2 ^ (m + 1)) = 2 * ((m + 1 : ℕ) : ℝ) * (4 : ℝ) ^ m := by
      rw [heq_m1, h4m1]
      push_cast
      ring
    have hle1 : P_gt 2 (2 ^ (m + 1)) ≤ 4 * (m : ℝ) * (4 : ℝ) ^ m := by
      rw [heq_m1']
      have : 2 * ((m + 1 : ℕ) : ℝ) ≤ 2 * (2 * (m : ℝ)) := by linarith
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) m]
    have hle2 : 4 * (m : ℝ) * (4 : ℝ) ^ m ≤ (4 / Real.log 2) * ((n : ℝ) ^ 2 * Real.log n) := by
      have hm_le : (m : ℝ) ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2_pos).mpr hlog_le
      calc 4 * (m : ℝ) * (4 : ℝ) ^ m
          ≤ 4 * (Real.log n / Real.log 2) * (n : ℝ) ^ 2 := by
            have h1 : 4 * (m : ℝ) ≤ 4 * (Real.log n / Real.log 2) := by linarith
            exact mul_le_mul h1 h4m_le (pow_nonneg (by norm_num) m)
              (mul_nonneg (by norm_num) (div_nonneg hlog_n_pos.le hlog2_pos.le))
        _ = (4 / Real.log 2) * ((n : ℝ) ^ 2 * Real.log n) := by ring
    have hlt_5 : 4 / Real.log 2 < 5 / Real.log 2 := div_lt_div_of_pos_right (by norm_num) hlog2_pos
    have hlt_5' : (4 / Real.log 2) * ((n : ℝ) ^ 2 * Real.log n) <
        (5 / Real.log 2) * ((n : ℝ) ^ 2 * Real.log n) :=
      mul_lt_mul_of_pos_right hlt_5 (mul_pos (sq_pos_of_pos hn_pos) hlog_n_pos)
    linarith

lemma P_gt_orderOf_gt2 {a : ℝ} (ha2 : 2 < a) :
    OrderOf (P_gt a) (fun n => (n : ℝ) ^ (1 + Real.log a / Real.log 2)) := by
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have ha_sub : 0 < a - 2 := by linarith
  let r := 1 + Real.log a / Real.log 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr_pos : 0 < r := by
    have : 0 < Real.log a / Real.log 2 := div_pos (Real.log_pos ha1) hlog2_pos
    linarith
  have hr_pow2 : (2 : ℝ) ^ r = 2 * a := by
    have h2 : (2 : ℝ) ^ (Real.log a / Real.log 2) = a := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      have heq : Real.log 2 * (Real.log a / Real.log 2) = Real.log a := by
        field_simp [hlog2_pos.ne']
      rw [heq, Real.exp_log ha0]
    dsimp [r]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, h2]
  have hpow2m_r : ∀ m : ℕ, ((2 ^ m : ℕ) : ℝ) ^ r = (2 * a) ^ m := by
    intro m
    push_cast
    rw [← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_comm (m : ℝ) r, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_natCast, hr_pow2]
  refine ⟨1 / (2 * a ^ 2), 3 * a / (a - 2),
    div_pos one_pos (by positivity), div_pos (by linarith) ha_sub, 2, fun n hn => ?_⟩
  let m := Nat.log 2 n
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact Nat.le_log_of_pow_le (by decide) hn
  have hpow_le : 2 ^ m ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hlt_pow : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hm_pow_ge1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have hmono1 : P_gt a (2 ^ m) ≤ P_gt a n := P_gt_mono ha1 hm_pow_ge1 hpow_le
  have hmono2 : P_gt a n ≤ P_gt a (2 ^ (m + 1)) := P_gt_mono ha1 (by omega) (le_of_lt hlt_pow)
  have hne2_m := P_gt_pow2_ne2 a m
  have hne2_m1 := P_gt_pow2_ne2 a (m + 1)
  have hdiff_ge : (a - 2) * a ^ (m - 1) ≤ a ^ m - (2 : ℝ) ^ m :=
    pow_sub_pow_ge (by norm_num) ha2.le m hm1
  have hlow_mul : ((a - 2) / a) * (2 * a) ^ m ≤ (2 * a) ^ m - (4 : ℝ) ^ m := by
    have heq1 : (2 * a) ^ m - (4 : ℝ) ^ m = (2 : ℝ) ^ m * (a ^ m - (2 : ℝ) ^ m) := by
      rw [← pow2_sq_eq_pow4 m, mul_pow]
      ring
    have heq2 : (2 : ℝ) ^ m * ((a - 2) * a ^ (m - 1)) = ((a - 2) / a) * (2 * a) ^ m := by
      have ha_m : a * a ^ (m - 1) = a ^ m := by
        rw [← pow_succ', Nat.sub_add_cancel hm1]
      calc (2 : ℝ) ^ m * ((a - 2) * a ^ (m - 1))
          = ((a - 2) / a) * ((2 : ℝ) ^ m * (a * a ^ (m - 1))) := by
            field_simp [ha0.ne']
        _ = ((a - 2) / a) * ((2 : ℝ) ^ m * a ^ m) := by rw [ha_m]
        _ = ((a - 2) / a) * (2 * a) ^ m := by ring
    rw [heq1, ← heq2]
    exact mul_le_mul_of_nonneg_left hdiff_ge (pow_nonneg (by norm_num) m)
  have hlow_2m : (1 / a) * (2 * a) ^ m ≤ P_gt a (2 ^ m) := by
    have heq : (a - 2) * P_gt a (2 ^ m) = (2 * a) ^ m - (4 : ℝ) ^ m := by linarith
    rw [← heq] at hlow_mul
    have hmul : (a - 2) * ((1 / a) * (2 * a) ^ m) ≤ (a - 2) * P_gt a (2 ^ m) := by
      have heq' : (a - 2) * ((1 / a) * (2 * a) ^ m) = ((a - 2) / a) * (2 * a) ^ m := by ring
      linarith
    exact le_of_mul_le_mul_left hmul ha_sub
  have hhigh_2m1 : P_gt a (2 ^ (m + 1)) ≤ (2 * a / (a - 2)) * (2 * a) ^ m := by
    have h4_nn : 0 ≤ (4 : ℝ) ^ (m + 1) := pow_nonneg (by norm_num) (m + 1)
    have hle : (a - 2) * P_gt a (2 ^ (m + 1)) ≤ (2 * a) ^ (m + 1) := by
      have : (a - 2) * P_gt a (2 ^ (m + 1)) = (2 * a) ^ (m + 1) - (4 : ℝ) ^ (m + 1) := by linarith
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀' ha_sub]
    have : (2 * a) ^ (m + 1) = (2 * a) * (2 * a) ^ m := by ring
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnr_pos : 0 < (n : ℝ) ^ r := Real.rpow_pos_of_pos hn_pos r
  have hnr_lt : (n : ℝ) ^ r < (2 * a) * (2 * a) ^ m := by
    have hlt : (n : ℝ) ^ r < ((2 ^ (m + 1) : ℕ) : ℝ) ^ r :=
      Real.rpow_lt_rpow hn_pos.le (by exact_mod_cast hlt_pow) hr_pos
    rw [hpow2m_r (m + 1)] at hlt
    have heq : (2 * a) ^ (m + 1) = (2 * a) * (2 * a) ^ m := by ring
    linarith
  have hnr_ge : (2 * a) ^ m ≤ (n : ℝ) ^ r := by
    have hle : ((2 ^ m : ℕ) : ℝ) ^ r ≤ (n : ℝ) ^ r :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpow_le) hr_pos.le
    rwa [hpow2m_r m] at hle
  constructor
  · have h1 : (1 / (2 * a ^ 2)) * (n : ℝ) ^ r < (1 / a) * (2 * a) ^ m := by
      have h2 : (1 / (2 * a ^ 2)) * (n : ℝ) ^ r < (1 / (2 * a ^ 2)) * ((2 * a) * (2 * a) ^ m) :=
        mul_lt_mul_of_pos_left hnr_lt (by positivity)
      have heq : (1 / (2 * a ^ 2)) * ((2 * a) * (2 * a) ^ m) = (1 / a) * (2 * a) ^ m := by
        field_simp [ha0.ne']
      linarith
    linarith
  · have hle : P_gt a n ≤ (2 * a / (a - 2)) * (n : ℝ) ^ r := by
      calc P_gt a n ≤ P_gt a (2 ^ (m + 1)) := hmono2
        _ ≤ (2 * a / (a - 2)) * (2 * a) ^ m := hhigh_2m1
        _ ≤ (2 * a / (a - 2)) * (n : ℝ) ^ r :=
          mul_le_mul_of_nonneg_left hnr_ge (div_nonneg (by linarith) ha_sub.le)
    have hlt : (2 * a / (a - 2)) * (n : ℝ) ^ r < (3 * a / (a - 2)) * (n : ℝ) ^ r := by
      have hdiv : 2 * a / (a - 2) < 3 * a / (a - 2) := div_lt_div_of_pos_right (by linarith) ha_sub
      exact mul_lt_mul_of_pos_right hdiv hnr_pos
    linarith

end ProofMO143865

theorem OMA.solution : type_of% @OMA.S_mo_143865.main := by
  intro a ha
  rcases lt_trichotomy a 1 with ha_lt1 | rfl | ha_gt1
  · -- Regime 1: 0 < a < 1
    have hrec : OMA.S_mo_143865.Recurs a (ProofMO143865.P_lt a) :=
      ProofMO143865.P_lt_recurs ha ha_lt1
    refine ⟨⟨ProofMO143865.P_lt a, hrec⟩, fun x hx => ?_⟩
    have hxy := ProofMO143865.recurs_unique hx hrec
    have hord1 : OMA.S_mo_143865.OrderOf x (fun n => (n : ℝ) ^ (1 : ℝ)) :=
      (ProofMO143865.orderOf_congr hxy).mpr (ProofMO143865.P_lt_orderOf ha ha_lt1)
    refine ⟨fun r _hr => ?_, fun ha2 => by linarith, fun i j hi hj => ?_⟩
    · constructor
      · intro hordr
        exact Or.inl ⟨ha_lt1, ProofMO143865.orderOf_rpow_unique hordr hord1⟩
      · rintro (⟨_, rfl⟩ | ⟨h1, _⟩ | ⟨h2, _⟩)
        · exact hord1
        · linarith
        · linarith
    · rw [ProofMO143865.cost_congr hxy hi hj]
      rw [(ProofMO143865.P_lt_min_aux ha ha_lt1 i j hi hj).2]
      constructor
      · intro h
        exact Or.inl ⟨ha_lt1, h⟩
      · rintro (⟨_, h⟩ | h1 | ⟨h1, _⟩)
        · exact h
        · linarith
        · linarith
  · -- Regime 2: a = 1
    have hrec : OMA.S_mo_143865.Recurs 1 ProofMO143865.P_eq := ProofMO143865.P_eq_recurs
    refine ⟨⟨ProofMO143865.P_eq, hrec⟩, fun x hx => ?_⟩
    have hxy := ProofMO143865.recurs_unique hx hrec
    have hord2 : OMA.S_mo_143865.OrderOf x (fun n => (n : ℝ) ^ (2 : ℝ)) :=
      (ProofMO143865.orderOf_congr hxy).mpr ProofMO143865.P_eq_orderOf
    refine ⟨fun r _hr => ?_, fun h => by norm_num at h, fun i j hi hj => ?_⟩
    · constructor
      · intro hordr
        exact Or.inr (Or.inl ⟨le_rfl, by norm_num, ProofMO143865.orderOf_rpow_unique hordr hord2⟩)
      · rintro (⟨h1, _⟩ | ⟨_, _, rfl⟩ | ⟨h2, _⟩)
        · linarith
        · exact hord2
        · linarith
    · rw [ProofMO143865.cost_congr hxy hi hj, ProofMO143865.P_eq_cost]
      exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => rfl⟩
  · -- Regime 3: 1 < a
    have hrec : OMA.S_mo_143865.Recurs a (ProofMO143865.P_gt a) :=
      ProofMO143865.P_gt_recurs ha_gt1
    refine ⟨⟨ProofMO143865.P_gt a, hrec⟩, fun x hx => ?_⟩
    have hxy := ProofMO143865.recurs_unique hx hrec
    refine ⟨fun r hr => ?_, fun ha2 => ?_, fun i j hi hj => ?_⟩
    · rcases lt_trichotomy a 2 with ha_lt2 | rfl | ha_gt2
      · have hord2 : OMA.S_mo_143865.OrderOf x (fun n => (n : ℝ) ^ (2 : ℝ)) :=
          (ProofMO143865.orderOf_congr hxy).mpr (ProofMO143865.P_gt_orderOf_lt2 ha_gt1 ha_lt2)
        constructor
        · intro hordr
          exact Or.inr (Or.inl ⟨ha_gt1.le, ha_lt2, ProofMO143865.orderOf_rpow_unique hordr hord2⟩)
        · rintro (⟨h1, _⟩ | ⟨_, _, rfl⟩ | ⟨h2, _⟩)
          · linarith
          · exact hord2
          · linarith
      · have hord_log : OMA.S_mo_143865.OrderOf x (fun n => (n : ℝ) ^ 2 * Real.log n) :=
          (ProofMO143865.orderOf_congr hxy).mpr ProofMO143865.P_gt_orderOf_eq2
        constructor
        · intro hordr
          exact False.elim (ProofMO143865.not_orderOf_rpow_of_sq_log hr hord_log hordr)
        · rintro (⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨h2, _⟩) <;> linarith
      · have hord_gt2 : OMA.S_mo_143865.OrderOf x (fun n => (n : ℝ) ^ (1 + Real.log a / Real.log 2)) :=
          (ProofMO143865.orderOf_congr hxy).mpr (ProofMO143865.P_gt_orderOf_gt2 ha_gt2)
        constructor
        · intro hordr
          exact Or.inr (Or.inr ⟨ha_gt2, ProofMO143865.orderOf_rpow_unique hordr hord_gt2⟩)
        · rintro (⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, rfl⟩)
          · linarith
          · linarith
          · exact hord_gt2
    · subst ha2
      exact (ProofMO143865.orderOf_congr hxy).mpr ProofMO143865.P_gt_orderOf_eq2
    · rw [ProofMO143865.cost_congr hxy hi hj]
      rw [(ProofMO143865.P_gt_min_aux ha_gt1 _ i j hi hj rfl).2]
      constructor
      · intro h
        exact Or.inr (Or.inr ⟨ha_gt1, h⟩)
      · rintro (⟨h1, _⟩ | h1 | ⟨_, h⟩)
        · linarith
        · linarith
        · exact h
