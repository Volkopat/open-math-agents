import OMAStatements.S_oeis_a111779
import Mathlib

namespace OMA.Helpers

open PowerSeries

noncomputable def cc (k : ℕ) : ℚ := ((2 * k).choose k : ℚ) / (4 : ℚ) ^ k

noncomputable def ch (i : ℕ) : ℚ := if i % 2 = 0 then cc (i / 2) else 0

noncomputable def bb (j : ℕ) : ℚ := ((j - 1).choose 4 : ℚ)

theorem cc_succ (k : ℕ) : (2 * (k : ℚ) + 2) * cc (k + 1) = (2 * k + 1) * cc k := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((k : ℚ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℚ) =
      2 * (2 * k + 1) * ((2 * k).choose k : ℚ) := by exact_mod_cast h
  unfold cc
  rw [pow_succ]
  field_simp
  linear_combination 2 * h'

theorem ch_rel (i : ℕ) : ((i : ℚ) + 2) * ch (i + 2) = (i + 1) * ch i := by
  unfold ch
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have h2 : (i + 2) % 2 = 0 := by omega
    rw [if_pos h2, if_pos h]
    obtain ⟨k, rfl⟩ : ∃ k, i = 2 * k := ⟨i / 2, by omega⟩
    have e1 : (2 * k + 2) / 2 = k + 1 := by omega
    have e2 : 2 * k / 2 = k := by omega
    rw [e1, e2]
    push_cast
    linear_combination cc_succ k
  · have h2 : (i + 2) % 2 = 1 := by omega
    rw [if_neg (by omega), if_neg (by omega)]
    ring

theorem bb_rel (m : ℕ) : ((m : ℚ) - 3) * bb (m + 2) = (m + 1) * bb (m + 1) := by
  unfold bb
  rcases Nat.lt_or_ge m 4 with hm | hm
  · interval_cases m <;> simp [Nat.choose]
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 4 := ⟨m - 4, by omega⟩
    have h1 := Nat.choose_succ_right_eq (p + 4) 3
    have h2 := Nat.add_one_mul_choose_eq (p + 4) 3
    have e : p + 4 - 3 = p + 1 := by omega
    rw [e] at h1
    have h1' : ((p + 4).choose 4 : ℚ) * 4 = ((p + 4).choose 3 : ℚ) * (p + 1) := by
      exact_mod_cast h1
    have h2' : ((p : ℚ) + 5) * ((p + 4).choose 3 : ℚ) = ((p + 5).choose 4 : ℚ) * 4 := by
      exact_mod_cast h2
    have e2 : p + 4 + 2 - 1 = p + 5 := by omega
    rw [e2]
    push_cast
    linear_combination (-(p + 1 : ℚ) / 4) * h2' - ((p + 5 : ℚ) / 4) * h1'

noncomputable def Cs : ℚ⟦X⟧ := PowerSeries.mk ch

noncomputable def Bs : ℚ⟦X⟧ := PowerSeries.mk bb

theorem hC : (1 - X ^ 2) * d⁄dX ℚ Cs = X * Cs := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_derivative]
  rcases n with _ | _ | m
  · simp [Cs, ch]
  · simp [Cs, ch, cc]
    norm_num
  · rw [if_pos (by omega), coeff_succ_X_mul, coeff_derivative]
    simp only [Cs, coeff_mk, show m + 2 - 2 = m by omega]
    have hr := ch_rel (m + 1)
    push_cast at hr ⊢
    linear_combination hr

theorem hB : X * (1 - X) * d⁄dX ℚ Bs = C (5 : ℚ) * Bs := by
  ext n
  rw [show X * (1 - X) * d⁄dX ℚ Bs = X * d⁄dX ℚ Bs - X ^ 2 * d⁄dX ℚ Bs by ring, map_sub,
    coeff_X_pow_mul', coeff_C_mul]
  rcases n with _ | _ | m
  · simp [Bs, bb]
  · simp [Bs, bb, coeff_derivative]
  · rw [if_pos (by omega), coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    simp only [Bs, coeff_mk, show m + 2 - 2 = m by omega]
    push_cast
    linear_combination bb_rel m

theorem hODE : X * (1 - X ^ 2) * d⁄dX ℚ (Cs * Bs) =
    (X ^ 2 + C (5 : ℚ) * X + C (5 : ℚ)) * (Cs * Bs) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  linear_combination (X * Bs) * hC + ((1 + X) * Cs) * hB

theorem g_rec (m : ℕ) : ((m : ℚ) - 2) * coeff (m + 3) (Cs * Bs) =
    5 * coeff (m + 2) (Cs * Bs) + ((m : ℚ) + 2) * coeff (m + 1) (Cs * Bs) := by
  have h : X * d⁄dX ℚ (Cs * Bs) - X ^ 3 * d⁄dX ℚ (Cs * Bs) =
      X ^ 2 * (Cs * Bs) + C (5 : ℚ) * (X * (Cs * Bs)) + C (5 : ℚ) * (Cs * Bs) := by
    linear_combination hODE
  have h2 := congrArg (coeff (m + 3)) h
  simp only [map_sub, map_add, coeff_succ_X_mul, coeff_C_mul, coeff_X_pow_mul', coeff_derivative,
    show 3 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, if_true, show m + 3 - 3 = m by omega,
    show m + 3 - 2 = m + 1 by omega] at h2
  push_cast at h2
  linear_combination h2

theorem sum_even_odd (f : ℕ → ℚ) (N : ℕ) :
    ∑ i ∈ Finset.range (2 * N), f i = ∑ k ∈ Finset.range N, (f (2 * k) + f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- The inner sum of the statement. -/
noncomputable def Sf (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range ((n - 5) / 2 + 1),
    ((2 * k).choose k : ℚ) * ((n - 2 * k - 1).choose 4 : ℚ) / (4 : ℚ) ^ k

theorem coeff_G (n : ℕ) : coeff n (Cs * Bs) = Sf n := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Cs, Bs, coeff_mk]
  have h1 : ∑ i ∈ Finset.range (n + 1), ch i * bb (n - i) =
      ∑ i ∈ Finset.range (2 * (n + 1)), ch i * bb (n - i) := by
    apply Finset.sum_subset
    · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    · intro i _ hi
      simp only [Finset.mem_range, not_lt] at hi
      simp [bb, show n - i = 0 by omega]
  rw [h1, sum_even_odd]
  have h2 : ∀ k, ch (2 * k) * bb (n - 2 * k) + ch (2 * k + 1) * bb (n - (2 * k + 1)) =
      cc k * bb (n - 2 * k) := by
    intro k
    have e1 : (2 * k) % 2 = 0 := by omega
    have e2 : (2 * k + 1) % 2 = 1 := by omega
    have e3 : 2 * k / 2 = k := by omega
    simp [ch, e1, e2, e3]
  simp only [h2]
  rw [Finset.sum_congr rfl (fun k _ => (show cc k * bb (n - 2 * k) =
    ((2 * k).choose k : ℚ) * ((n - 2 * k - 1).choose 4 : ℚ) / (4 : ℚ) ^ k by
      unfold cc bb; ring))]
  unfold Sf
  symm
  apply Finset.sum_subset
  · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [Nat.choose_eq_zero_of_lt (show n - 2 * k - 1 < 4 by omega)]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a111779.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hr := g_rec m
  rw [coeff_G, coeff_G, coeff_G] at hr
  have ea : ∀ k, OMA.S_oeis_a111779.a k = (k.factorial : ℚ) / (Nat.factorial 5 : ℚ) * Sf k :=
    fun k => rfl
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, ea, ea, ea]
  simp only [Nat.factorial_succ]
  push_cast
  linear_combination (-((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) / 120) * hr
