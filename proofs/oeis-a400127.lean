import OMAStatements.S_oeis_a400127
import Mathlib

open OMA.S_oeis_a400127

namespace OMA.P_a400127

theorem core (α : ℝ) (hα : 0 < α) (hne : ∀ q : ℕ, ∀ p : ℤ, 0 < q → (q:ℝ) * α ≠ p)
    (L U : ℝ) (hL : 0 ≤ L) (hLU : L < U) :
    ∃ k : ℕ, ∃ j : ℤ, 0 ≤ j ∧ (j:ℝ) + L ≤ k * α ∧ (k:ℝ) * α < j + U := by
  set δ : ℝ := min (U - L) (1/2) with hδ
  have hδpos : 0 < δ := by rw [hδ]; apply lt_min <;> linarith
  have hδ1 : δ ≤ U - L := min_le_left _ _
  have hδ2 : δ ≤ 1/2 := min_le_right _ _
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : 0 < N := by
    have : (0:ℝ) < N := lt_trans (by positivity) hN
    exact_mod_cast this
  obtain ⟨q, hq, -, hqe⟩ := Real.exists_nat_abs_mul_sub_round_le α hNpos
  set p : ℤ := round ((q:ℝ) * α) with hp
  set e : ℝ := (q:ℝ) * α - p with he
  have hNδ : 1 / ((N:ℝ) + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδpos] at hN
    nlinarith
  have hea : |e| < δ := lt_of_le_of_lt hqe hNδ
  have he0 : e ≠ 0 := by
    intro h0; apply hne q p hq; rw [he] at h0; linarith
  have hqα : (1:ℝ) * α ≤ q * α := by
    apply mul_le_mul_of_nonneg_right _ hα.le; exact_mod_cast hq
  have hU : 0 < U := by linarith
  rcases lt_or_gt_of_ne he0 with hneg | hpos
  · -- e < 0
    set f : ℝ := -e with hf
    have hfpos : 0 < f := by linarith
    have hfδ : f < δ := by rw [abs_of_neg hneg] at hea; linarith
    obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, 2 * U ≤ N0 := ⟨⌈2 * U⌉₊, Nat.le_ceil _⟩
    have hx : 0 ≤ ((N0:ℝ) - U) / f := by apply div_nonneg _ hfpos.le; linarith
    set m : ℕ := ⌊((N0:ℝ) - U) / f⌋₊ + 1 with hm
    have hm1 : ((N0:ℝ) - U) / f < m := by rw [hm]; push_cast; exact Nat.lt_floor_add_one _
    have hm2 : (m:ℝ) ≤ ((N0:ℝ) - U) / f + 1 := by
      rw [hm]; push_cast; linarith [Nat.floor_le hx]
    have hA : (N0:ℝ) - U < m * f := by rwa [div_lt_iff₀ hfpos] at hm1
    have hB : (m:ℝ) * f ≤ (N0:ℝ) - U + f := by
      have := mul_le_mul_of_nonneg_right hm2 hfpos.le
      rw [add_mul, div_mul_cancel₀ _ hfpos.ne'] at this; linarith
    have hp1 : (1:ℤ) ≤ p := by
      have : (0:ℝ) < p := by rw [he] at hf; linarith
      have : (0:ℤ) < p := by exact_mod_cast this
      omega
    have hmN : (N0:ℝ) ≤ m := by
      have h2 : 2 * ((N0:ℝ) - U) ≤ ((N0:ℝ) - U) / f := by
        rw [le_div_iff₀ hfpos]; nlinarith
      linarith
    have hmN' : N0 ≤ m := by exact_mod_cast hmN
    refine ⟨m * q, (m:ℤ) * p - N0, ?_, ?_, ?_⟩
    · have : (m:ℤ) ≤ m * p := by nlinarith
      omega
    · push_cast
      have : (m:ℝ) * q * α = m * p - m * f := by rw [hf, he]; ring
      rw [this]; linarith
    · push_cast
      have : (m:ℝ) * q * α = m * p - m * f := by rw [hf, he]; ring
      rw [this]; linarith
  · -- e > 0
    have heδ : e < δ := by rw [abs_of_pos hpos] at hea; exact hea
    have hp0 : (0:ℤ) ≤ p := by
      have : (-1:ℝ) < p := by rw [he] at heδ; linarith
      have : (-1:ℤ) < p := by exact_mod_cast this
      omega
    have hx : 0 ≤ L / e := div_nonneg hL hpos.le
    set m : ℕ := ⌈L / e⌉₊ with hm
    have hm1 : L ≤ m * e := by rw [← div_le_iff₀ hpos]; exact Nat.le_ceil _
    have hm2 : (m:ℝ) * e < L + e := by
      have := Nat.ceil_lt_add_one hx
      rw [← hm] at this
      have := mul_lt_mul_of_pos_right this hpos
      rw [add_mul, div_mul_cancel₀ _ hpos.ne'] at this; linarith
    refine ⟨m * q, (m:ℤ) * p, by positivity, ?_, ?_⟩
    · push_cast
      have : (m:ℝ) * q * α = m * p + m * e := by rw [he]; ring
      rw [this]; linarith
    · push_cast
      have : (m:ℝ) * q * α = m * p + m * e := by rw [he]; ring
      rw [this]; linarith

theorem hne3 : ∀ q : ℕ, ∀ p : ℤ, 0 < q → (q:ℝ) * (Real.log 3 / Real.log 2) ≠ p := by
  intro q p hq h
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have key : (q:ℝ) * Real.log 3 = p * Real.log 2 := by
    field_simp at h; linarith
  have hp : 0 ≤ p := by
    by_contra hcon
    have : (p:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hcon)
    nlinarith
  lift p to ℕ using hp
  have e1 : Real.log ((3:ℝ) ^ q) = Real.log ((2:ℝ) ^ p) := by
    rw [Real.log_pow, Real.log_pow]; push_cast at key; linarith
  have e2 : (3:ℝ) ^ q = (2:ℝ) ^ p :=
    Real.log_injOn_pos (by simp) (by simp) e1
  have e3 : (3:ℕ) ^ q = 2 ^ p := by exact_mod_cast e2
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    have : 3 ^ 1 ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) hq
    simp at e3; omega
  · have a1 : 3 ^ q % 2 = 1 := by rw [Nat.pow_mod]; simp
    have a2 : 2 ^ p % 2 = 0 := by
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      rw [pow_succ]; simp
    omega

theorem word (n w : ℕ) (hn : 1 ≤ n) (hw : w < 2 ^ n) : ∃ k : ℕ, occurs n w (3 ^ k) := by
  set A : ℕ := 2 ^ n + w with hA
  have hApos : (0:ℝ) < A := by positivity
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hA1 : (1:ℝ) ≤ A := by
    have : 1 ≤ A := by rw [hA]; have := Nat.one_le_two_pow (n := n); omega
    exact_mod_cast this
  have hL : 0 ≤ Real.log A / Real.log 2 := div_nonneg (Real.log_nonneg hA1) h2.le
  have hLU : Real.log A / Real.log 2 < Real.log ((A:ℝ) + 1) / Real.log 2 := by
    apply div_lt_div_of_pos_right _ h2
    exact Real.log_lt_log hApos (by linarith)
  obtain ⟨k, j, hj, hlo, hhi⟩ := core (Real.log 3 / Real.log 2) (div_pos h3 h2) hne3 _ _ hL hLU
  lift j to ℕ using hj
  have lo : (j:ℝ) * Real.log 2 + Real.log A ≤ k * Real.log 3 := by
    have := mul_le_mul_of_nonneg_right hlo h2.le
    field_simp at this; push_cast at this ⊢; linarith
  have hi : (k:ℝ) * Real.log 3 < j * Real.log 2 + Real.log ((A:ℝ) + 1) := by
    have := mul_lt_mul_of_pos_right hhi h2
    field_simp at this; push_cast at this ⊢; linarith
  have lo' : (2:ℝ) ^ j * A ≤ 3 ^ k := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
      hApos.ne', Real.log_pow, Real.log_pow]
    linarith
  have hi' : (3:ℝ) ^ k < 2 ^ j * (A + 1) := by
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow]
    linarith
  have lo'' : 2 ^ j * A ≤ 3 ^ k := by exact_mod_cast lo'
  have hi'' : 3 ^ k < 2 ^ j * (A + 1) := by exact_mod_cast hi'
  refine ⟨k, j, ?_, ?_⟩
  · calc 2 ^ (j + n - 1) ≤ 2 ^ (j + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ j * 2 ^ n := pow_add _ _ _
      _ ≤ 2 ^ j * A := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 3 ^ k := lo''
  · have : 3 ^ k / 2 ^ j = A := by
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm]; exact lo''
      · rw [mul_comm]; exact hi''
    rw [this, hA, Nat.add_mod_left, Nat.mod_eq_of_lt hw]

end OMA.P_a400127

open OMA.P_a400127

theorem OMA.solution : type_of% @OMA.S_oeis_a400127.main := by
  intro n hn
  have h : ∀ w, ∃ k, (w < 2 ^ n → occurs n w (3 ^ k)) := by
    intro w
    by_cases hw : w < 2 ^ n
    · obtain ⟨k, hk⟩ := word n w hn hw
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose g hg using h
  refine ⟨∑ w ∈ Finset.range (2 ^ n), g w, fun w hw => ⟨g w, ?_, hg w hw⟩⟩
  exact Finset.single_le_sum (f := g) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hw)
