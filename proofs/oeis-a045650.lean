import OMAStatements.S_oeis_a045650
import Mathlib

namespace OMA.P045650

open OMA.S_oeis_a045650 Filter Asymptotics

/-- `S 0 = 0` and, for `j ≥ 1`, `S j = ⌈e^j⌉ + j - 1`: values that are not of the form `k + ⌊log k⌋`. -/
noncomputable def S (j : ℕ) : ℕ := if j = 0 then 0 else ⌈Real.exp (j : ℝ)⌉₊ + j - 1

lemma ceil_ge_one (j : ℕ) : 1 ≤ ⌈Real.exp (j : ℝ)⌉₊ :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

lemma S_lt_succ (j : ℕ) : S j < S (j + 1) := by
  unfold S
  have h1 := ceil_ge_one j
  have h2 := ceil_ge_one (j + 1)
  have h3 : ⌈Real.exp (j : ℝ)⌉₊ ≤ ⌈Real.exp ((j + 1 : ℕ) : ℝ)⌉₊ :=
    Nat.ceil_mono (Real.exp_le_exp.mpr (by push_cast; linarith))
  have hne : ¬ (j + 1 = 0) := by omega
  by_cases hj : j = 0
  · rw [if_pos hj, if_neg hne]
    omega
  · rw [if_neg hj, if_neg hne]
    omega

lemma S_strictMono : StrictMono S := strictMono_nat_of_lt_succ S_lt_succ

lemma P_S (j : ℕ) : P (S j) := by
  unfold P
  rintro ⟨k, hk1, hk⟩
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk1' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
  by_cases hj : j = 0
  · have hS : S j = 0 := by rw [S, if_pos hj]
    rw [hS] at hk
    have h0 : (0 : ℤ) ≤ ⌊Real.log (k : ℝ)⌋ :=
      Int.floor_nonneg.mpr (Real.log_nonneg (by exact_mod_cast hk1))
    push_cast at hk
    omega
  · have hS : S j = ⌈Real.exp (j : ℝ)⌉₊ + j - 1 := by rw [S, if_neg hj]
    have hc1 := ceil_ge_one j
    have hle : Real.exp (j : ℝ) ≤ (⌈Real.exp (j : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have hlt : (⌈Real.exp (j : ℝ)⌉₊ : ℝ) < Real.exp (j : ℝ) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    rw [hS] at hk
    have hcast : ((⌈Real.exp (j : ℝ)⌉₊ + j - 1 : ℕ) : ℤ) = (⌈Real.exp (j : ℝ)⌉₊ : ℤ) + (j : ℤ) - 1 := by
      omega
    rw [hcast] at hk
    rcases le_or_gt ⌈Real.exp (j : ℝ)⌉₊ k with hck | hck
    · have h1 : (j : ℝ) ≤ Real.log (k : ℝ) := by
        rw [Real.le_log_iff_exp_le hkpos]
        exact hle.trans (by exact_mod_cast hck)
      have h2 : (j : ℤ) ≤ ⌊Real.log (k : ℝ)⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
      have h3 : (⌈Real.exp (j : ℝ)⌉₊ : ℤ) ≤ (k : ℤ) := by exact_mod_cast hck
      omega
    · have h1 : Real.log (k : ℝ) < (j : ℝ) := by
        rw [Real.log_lt_iff_lt_exp hkpos]
        have h4 : (k : ℝ) + 1 ≤ (⌈Real.exp (j : ℝ)⌉₊ : ℝ) := by exact_mod_cast hck
        linarith
      have h2 : ⌊Real.log (k : ℝ)⌋ < (j : ℤ) := Int.floor_lt.mpr (by exact_mod_cast h1)
      have h3 : (k : ℤ) + 1 ≤ (⌈Real.exp (j : ℝ)⌉₊ : ℤ) := by exact_mod_cast hck
      omega

open Classical in
lemma a_le (n : ℕ) (hn : 1 ≤ n) : a n ≤ S (n - 1) := by
  unfold a
  have hcount : n - 1 < Nat.count P (S (n - 1) + 1) := by
    rw [Nat.count_eq_card_filter_range]
    refine lt_of_lt_of_le (by omega : n - 1 < n) ?_
    refine le_trans (le_of_eq (Finset.card_range n).symm) ?_
    apply Finset.card_le_card_of_injOn S
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_range] at hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (S_strictMono.monotone (by omega)), P_S j⟩
    · exact S_strictMono.injective.injOn
  exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hcount)

end OMA.P045650

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a045650.main) := by
  intro h
  have hv : ∀ᶠ n : ℕ in Filter.atTop, Real.exp (n : ℝ) ≠ 0 :=
    Filter.Eventually.of_forall (fun n => (Real.exp_pos _).ne')
  have ht := (Asymptotics.isEquivalent_iff_tendsto_one hv).mp h
  have hev := (tendsto_order.1 ht).1 (9 / 10) (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := (hev.and (Filter.eventually_ge_atTop 2)).exists
  simp only [Pi.div_apply] at hn1
  have hb := OMA.P045650.a_le n (by omega)
  have hS : OMA.P045650.S (n - 1) = ⌈Real.exp ((n - 1 : ℕ) : ℝ)⌉₊ + (n - 1) - 1 := by
    rw [OMA.P045650.S, if_neg (by omega)]
  have hc : (⌈Real.exp ((n - 1 : ℕ) : ℝ)⌉₊ : ℝ) < Real.exp ((n - 1 : ℕ) : ℝ) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hnat : OMA.S_oeis_a045650.a n + 1 ≤ ⌈Real.exp ((n - 1 : ℕ) : ℝ)⌉₊ + n := by
    rw [hS] at hb
    omega
  have hreal : (OMA.S_oeis_a045650.a n : ℝ) + 1 ≤ (⌈Real.exp ((n - 1 : ℕ) : ℝ)⌉₊ : ℝ) + (n : ℝ) := by
    exact_mod_cast hnat
  have hcast : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hexp : (n : ℝ) ≤ Real.exp ((n - 1 : ℕ) : ℝ) := by
    have h5 := Real.add_one_le_exp (((n - 1 : ℕ)) : ℝ)
    rw [hcast] at h5 ⊢
    linarith
  have he : Real.exp (n : ℝ) = Real.exp ((n - 1 : ℕ) : ℝ) * Real.exp 1 := by
    rw [← Real.exp_add, hcast]
    congr 1
    ring
  have he1 := Real.exp_one_gt_d9
  have hpos : 0 < Real.exp ((n - 1 : ℕ) : ℝ) := Real.exp_pos _
  rw [lt_div_iff₀ (Real.exp_pos _), he] at hn1
  have h6 := mul_lt_mul_of_pos_left he1 hpos
  linarith
